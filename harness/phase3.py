#!/usr/bin/env python3
"""Phase 3: search for matrix-interpretation proofs across encodings.

Every problem is a rewriting system in one of two search forms (harness/systems.py,
`search_problem`).  For each problem the published prover is run over a grid of interpretation
types, dimensions and coefficient ranges, smallest first, each run under a time limit, until
one run proves the problem or the grid is exhausted.  Every proof found, complete or partial,
is verified by checker/check.py.

Problem groups
    control    statements the paper proved: a search that cannot find these is too weak
    target     statements the paper leaves open (residue classes 1, 5, 7 and "5 or 7" mod 8)
    full       the Collatz conjecture itself, in every encoding
    negative   systems that are known to loop: a proof here would be a bug

Runs are appended to results/phase3/runs.jsonl as they finish, and a run already recorded
there is not repeated, so the search can be stopped and resumed.

Usage:
    phase3.py --list                       show the problems
    phase3.py --validate                   check the new systems against their maps
    phase3.py --run GROUP... [options]     run the search for the given groups
    phase3.py --report                     write results/phase3/summary.md
"""
import argparse
import json
import os
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'checker'))

import systems as sy                                                    # noqa: E402
from check import CertificateError, check                              # noqa: E402
from checks import Failure, check_rules, lemma_certificates, need, simulate  # noqa: E402

PROBLEMS = os.path.join(ROOT, 'problems', 'phase3')
RESULTS = os.path.join(ROOT, 'results', 'phase3')
CERTS = os.path.join(RESULTS, 'certificates')
RUNS = os.path.join(RESULTS, 'runs.jsonl')

T, S = sy.COLLATZ, sy.SHIFTED
BLOCKS = (2, 3, 4, 5, 6)

# Residue-class statements about non-convergent trajectories: (modulus, classes, status).
STATEMENTS = [
    (4, {1}, 'control'), (4, {3}, 'control'),
    (8, {3}, 'control'), (8, {1, 5}, 'control'), (8, {1, 7}, 'control'),
    (8, {1}, 'target'), (8, {5}, 'target'), (8, {7}, 'target'), (8, {5, 7}, 'target'),
]


def encodings(modulus):
    """The four encodings in which a statement modulo 4 or 8 is posed."""
    bits = {4: 2, 8: 3}[modulus]
    return [sy.contextual(T, bits), sy.contextual(S, bits),
            sy.accelerate(T, bits), sy.accelerate(S, bits)]


def all_problems():
    out = []

    def add(group, system, statement):
        for side in ('left', 'right'):
            out.append({'name': f'{system.name}.{side}', 'group': group, 'system': system,
                        'side': side, 'statement': statement, 'encoding': system.name})

    for modulus, classes, group in STATEMENTS:
        tag = ' or '.join(str(c) for c in sorted(classes))
        for base in encodings(modulus):
            system = base.without_classes(modulus, classes)
            add(group, system, f'visits {tag} mod {modulus}')
            out[-1]['encoding'] = out[-2]['encoding'] = base.name
    full = [T, S, sy.SHIFTED_TWO_MARKERS, sy.contextual(T, 2), sy.contextual(S, 2),
            sy.contextual(T, 3), sy.contextual(S, 3)]
    full += [sy.accelerate(base, k) for k in BLOCKS for base in (T, S)]
    for system in full:
        add('full', system, 'Collatz conjecture')
    siblings = [sy.THREE_N_MINUS_ONE, sy.SHIFTED_THREE_N_MINUS_ONE, sy.FIVE_N_PLUS_ONE]
    for system in siblings + [sy.accelerate(b, k) for k in (2, 3, 4) for b in siblings]:
        add('negative', system, 'none: the system loops')
    return out


def grid(max_dimension):
    """(type, dimension, coefficient values), roughly smallest search space first."""
    configs = []
    for d in range(1, max_dimension + 1):
        for w in (2, 3, 4, 6, 8, 11) if d <= 3 else (2, 3, 4):
            configs.append(('natural', d, w))
        for w in (3, 4, 6, 8) if d <= 3 else (3, 4):
            configs.append(('arctic', d, w))
    return sorted(configs, key=lambda c: (c[1] ** 3 * c[2] ** 2, c[0]))


# ---------------------------------------------------------------------------------------
# Validation of the systems that are new in this phase
# ---------------------------------------------------------------------------------------

def validate():
    """The context systems do the arithmetic they claim and stop only where intended; a
    dynamic rule applies to the binary string of n exactly when n is outside the removed
    classes (for every n large enough to have enough digits)."""
    for bits in (2, 3):
        for base in (T, S):
            system = sy.contextual(base, bits)
            check_rules(system)
            lemma_certificates(system, PROBLEMS, RESULTS, which=('left',))
            simulate(system, 400, 4, 4)
            print(f'{system.name}: {len(system.rules)} rules, arithmetic, lemma and '
                  'simulation hold', flush=True)
    for problem in all_problems():
        system = problem['system']
        if problem['group'] not in ('control', 'target') or problem['side'] != 'left':
            continue
        modulus = int(problem['statement'].split('mod ')[1])
        classes = {int(c) for c in problem['statement'].split('mod')[0].split()[1:] if c != 'or'}
        shift = system.lowest - 1
        for n in range(64, 64 + 4 * 256):
            string = system.encode(n + shift)
            applies = any(string.endswith(l) for l, _ in system.dynamic)
            if system.power > 1:
                expected = n % modulus not in classes
            else:       # single-step systems only split the growing (odd n) step
                expected = n % 2 == 0 or n % modulus not in classes
            need(applies == expected, f'{system.name}: wrong rule coverage at n = {n}')
    print('rule coverage of every control and target system matches its statement')


# ---------------------------------------------------------------------------------------
# Running the prover
# ---------------------------------------------------------------------------------------

LOCK = threading.Lock()


def load_runs():
    runs = []
    if os.path.exists(RUNS):
        with open(RUNS) as f:
            runs = [json.loads(line) for line in f if line.strip()]
    return runs


def verify(problem_file, cert_file):
    """(verdict, steps, rules removed, strict rules remaining) for a saved certificate."""
    try:
        with open(problem_file) as f:
            text = f.read()
        with open(cert_file) as f:
            cert = json.load(f)
    except (OSError, ValueError):
        return 'no certificate', 0, 0, None
    if not cert.get('steps'):
        return 'no steps', 0, 0, None
    try:
        result = check(text, cert, allow_partial=True)
    except CertificateError as e:
        return f'REJECTED: {e}', 0, 0, None
    removed = sum(len(step['removed']) for step in result['steps'])
    return 'accepted', len(result['steps']), removed, len(result['remaining_strict'])


def run_one(problem, config, timeout):
    kind, d, w = config
    problem_file = os.path.join(PROBLEMS, problem['name'] + '.srs')
    cert_file = os.path.join(CERTS, f'{problem["name"]}__{kind}-d{d}-w{w}.json')
    cmd = [sys.executable, os.path.join(HERE, 'run_published.py'), problem_file, cert_file,
           '-i', kind, '-d', str(d), '-rw', str(w), '-any', '--no-print', '-work', '1',
           '-noshuf']
    start = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                            start_new_session=True)
    try:
        code = proc.wait(timeout=timeout)
        status = None
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
        code, status = None, 'timeout'
    seconds = time.time() - start
    verdict, steps, removed, remaining = verify(problem_file, cert_file)
    if status is None:
        try:
            with open(cert_file) as f:
                status = json.load(f)['prover']['status']
        except (OSError, ValueError, KeyError):
            status = f'error (exit {code})'
    if status == 'QED' and not (verdict == 'accepted' and remaining == 0):
        status = 'QED claimed but not verified'
    if steps == 0 and os.path.exists(cert_file):
        os.remove(cert_file)                # nothing worth keeping
    return {'problem': problem['name'], 'group': problem['group'], 'type': kind,
            'dimension': d, 'values': w, 'timeout': timeout, 'status': status,
            'seconds': round(seconds, 1), 'steps': steps, 'removed': removed,
            'remaining': remaining, 'checker': verdict}


def run_problem(problem, configs, timeout, done):
    for config in configs:
        key = (problem['name'],) + config
        if key in done:
            if done[key]['status'] == 'QED':
                return
            if done[key]['status'] != 'timeout' or done[key]['timeout'] >= timeout:
                continue
        record = run_one(problem, config, timeout)
        with LOCK:
            with open(RUNS, 'a') as f:
                f.write(json.dumps(record) + '\n')
            print(f'{record["problem"]:34s} {record["type"]:8s} d={record["dimension"]} '
                  f'w={record["values"]:<3d} {record["status"]:10s} {record["seconds"]:6.1f} s  '
                  f'removed {record["removed"]}', flush=True)
        if record['status'] == 'QED':
            return


def run(groups, timeout, jobs, max_dimension, only):
    os.makedirs(CERTS, exist_ok=True)
    problems = [p for p in all_problems() if p['group'] in groups]
    if only:
        problems = [p for p in problems if any(o in p['name'] for o in only)]
    for p in problems:
        with open(os.path.join(PROBLEMS, p['name'] + '.srs'), 'w') as f:
            f.write(p['system'].search_problem(p['side']))
    done = {}
    for r in load_runs():
        key = (r['problem'], r['type'], r['dimension'], r['values'])
        if key not in done or r['timeout'] >= done[key]['timeout'] or r['status'] == 'QED':
            done[key] = r
    solved = {k[0] for k, r in done.items() if r['status'] == 'QED'}
    problems = [p for p in problems if p['name'] not in solved]
    configs = grid(max_dimension)
    print(f'{len(problems)} problems, {len(configs)} configurations each, '
          f'{timeout} s per run, {jobs} at a time', flush=True)
    with ThreadPoolExecutor(jobs) as pool:
        list(pool.map(lambda p: run_problem(p, configs, timeout, done), problems))


# ---------------------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------------------

def report():
    runs = load_runs()
    by_problem = {}
    for r in runs:
        by_problem.setdefault(r['problem'], []).append(r)
    problems = {p['name']: p for p in all_problems()}
    size = lambda r: (r['dimension'] ** 3 * r['values'] ** 2, r['type'])
    out = []
    say = out.append

    def cell(name):
        rs = by_problem.get(name)
        if not rs:
            return 'not run'
        proofs = [r for r in rs if r['status'] == 'QED']
        if proofs:
            best = min(proofs, key=size)
            return (f'**proved**: {best["type"]}, dimension {best["dimension"]}, '
                    f'{best["values"]} values, {best["seconds"]:.0f} s')
        latest = {}
        for r in rs:
            latest[(r['type'], r['dimension'], r['values'])] = r
        unsat = sum(r['status'] == 'UNSAT' for r in latest.values())
        timed = sum(r['status'] == 'timeout' for r in latest.values())
        other = len(latest) - unsat - timed
        best = max(latest.values(), key=lambda r: r['removed'])
        text = f'no proof: {unsat} ruled out, {timed} timed out'
        if other:
            text += f', {other} other'
        if best['removed']:
            text += (f'; best partial removes {best["removed"]} strict rule(s), leaves '
                     f'{best["remaining"]}')
        return text

    say('# Phase 3 results')
    say()
    say('Produced by `harness/phase3.py --report` from `results/phase3/runs.jsonl`.')
    say()
    say('- "proved" means the published prover found a complete proof and `checker/check.py`')
    say('  accepted it. The smallest configuration that succeeded is shown.')
    say('- "ruled out" counts configurations for which the SAT solver reported that no')
    say('  interpretation of that type, dimension and coefficient range exists. These verdicts')
    say('  come from the solver alone and are not independently certified.')
    say('- "timed out" counts configurations that reached the time limit undecided. A timeout')
    say('  says nothing either way.')
    say('- "left" and "right" are the two search forms: left-end rules strict at the left end,')
    say('  or dynamic rules strict at the right end. A proof in either form is a proof.')
    timeouts = sorted({r['timeout'] for r in runs})
    dims = sorted({r['dimension'] for r in runs})
    say()
    say(f'{len(runs):,} prover runs are recorded, with time limits of '
        f'{", ".join(str(t) for t in timeouts)} seconds and dimensions '
        f'{dims[0]} to {dims[-1]}.' if runs else 'No runs recorded.')

    for group, title, intro in (
            ('control', 'Controls: statements the paper proved',
             'Every non-convergent Collatz trajectory visits the given residue class.'),
            ('target', 'Targets: statements the paper leaves open',
             'Every non-convergent Collatz trajectory visits the given residue class.')):
        say()
        say(f'## {title}')
        say()
        say(intro + ' For block encodings (`T.k`, `S.k`) the statement proved is stronger: the')
        say('class is visited at a step count that is a multiple of the block size.')
        statements = []
        for modulus, classes, g in STATEMENTS:
            if g == group:
                statements.append((modulus, classes))
        for modulus, classes in statements:
            tag = ' or '.join(str(c) for c in sorted(classes))
            say()
            say(f'### Visits {tag} mod {modulus}')
            say()
            say('| Encoding | Rules | Left form | Right form |')
            say('|---|---|---|---|')
            for base in encodings(modulus):
                system = base.without_classes(modulus, classes)
                say(f'| {base.name} | {len(system.rules)} | {cell(system.name + ".left")} | '
                    f'{cell(system.name + ".right")} |')

    for group, title, intro in (
            ('full', 'The Collatz conjecture itself',
             'Each system terminates if and only if the conjecture is true.'),
            ('negative', 'Negative controls: systems that loop',
             'Each of these has an explicit loop, so "proved" in this table would be a bug. '
             'Partial removals are legitimate: a looping system can still have rules that are '
             'used only finitely often.')):
        say()
        say(f'## {title}')
        say()
        say(intro)
        say()
        say('| System | Rules | Left form | Right form |')
        say('|---|---|---|---|')
        seen = []
        for p in problems.values():
            if p['group'] == group and p['system'].name not in seen:
                seen.append(p['system'].name)
                say(f'| {p["system"].name} | {len(p["system"].rules)} | '
                    f'{cell(p["system"].name + ".left")} | {cell(p["system"].name + ".right")} |')

    bad = [r for r in runs if r['group'] == 'negative' and r['status'] == 'QED']
    odd = [r for r in runs if r['status'] not in ('QED', 'UNSAT', 'timeout')]
    rejected = [r for r in runs if r['checker'].startswith('REJECTED')]
    say()
    say('## Integrity')
    say()
    say(f'- Proofs reported for looping systems: {len(bad)}.')
    say(f'- Certificates rejected by the checker: {len(rejected)}.')
    say(f'- Runs that ended in an error instead of a verdict: {len(odd)}.')
    with open(os.path.join(RESULTS, 'summary.md'), 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('\n'.join(out))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--validate', action='store_true')
    ap.add_argument('--run', nargs='+', choices=['control', 'target', 'full', 'negative'])
    ap.add_argument('--report', action='store_true')
    ap.add_argument('--timeout', type=int, default=60)
    ap.add_argument('--jobs', type=int, default=os.cpu_count() or 1)
    ap.add_argument('--max-dimension', type=int, default=3)
    ap.add_argument('--only', nargs='+', help='restrict to problems whose name contains this')
    args = ap.parse_args()
    os.makedirs(PROBLEMS, exist_ok=True)
    os.makedirs(RESULTS, exist_ok=True)
    if args.list:
        for p in all_problems():
            print(f'{p["group"]:9s} {p["name"]:34s} {len(p["system"].rules):3d} rules  '
                  f'{p["statement"]}')
    if args.validate:
        validate()
    if args.run:
        run(args.run, args.timeout, args.jobs, args.max_dimension, args.only)
    if args.report:
        report()


if __name__ == '__main__':
    try:
        main()
    except Failure as e:
        print(f'FAILED: {e}')
        sys.exit(1)
