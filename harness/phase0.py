#!/usr/bin/env python3
"""Phase 0: reproduce the published "one rule left out" proofs and check them independently.

For each of the 11 rules of the Collatz system T, the paper proves that T without that rule
terminates.  This script

  1. writes the 11 problems from our own definition of T (harness/systems.py) and confirms
     they are the same problems as the files published with the paper;
  2. runs the published prover on each, with the published search parameters;
  3. verifies every certificate with checker/check.py, which shares no code with the prover;
  4. verifies the two hand-written interpretations of Lemma 3.15 of the paper;
  5. writes results/phase0/summary.md.

Usage:  phase0.py [--timeout SECONDS] [problem numbers...]
"""
import argparse
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'checker'))

import systems                                            # noqa: E402
from check import CertificateError, check                # noqa: E402

UPSTREAM = os.path.join(ROOT, 'third_party', 'rewriting-collatz')
PROBLEMS = os.path.join(ROOT, 'problems', 'phase0')
RESULTS = os.path.join(ROOT, 'results', 'phase0')

# Search parameters from the published proofs.sh: interpretation type, dimension, and the
# number of values a coefficient may take.
PUBLISHED = {1: ('natural', 3, 4), 2: ('natural', 1, 2), 3: ('natural', 4, 2),
             4: ('natural', 1, 3), 5: ('natural', 1, 2), 6: ('arctic', 3, 4),
             7: ('arctic', 4, 3), 8: ('arctic', 2, 5), 9: ('natural', 2, 2),
             10: ('natural', 3, 3), 11: ('arctic', 4, 3)}

PAPER_NAMES = {'a': 'f', 'b': 't', 'c': '◁', 'd': '▷', 'e': '0', 'f': '1', 'g': '2'}


def paper(rule):
    l, r = rule
    return f'{"".join(PAPER_NAMES[s] for s in l)} → {"".join(PAPER_NAMES[s] for s in r)}'


def rule_set(text):
    return sorted(tuple(line.split()) for line in text.splitlines() if line.strip())


# Lemma 3.15 of the paper, on the reversed systems (one-dimensional natural interpretations).
def lemma_3_15():
    affine = lambda m, c: {'M': [[m]], 'v': [c]}
    no_left = systems.DYNAMIC + systems.CARRY                 # T without the left-end rules
    no_dyn = systems.CARRY + systems.LEFT                     # T without the dynamic rules
    cases = {
        'lemma-3.15-T-without-left-end-rules-reversed': (
            no_left,
            {'a': affine(2, 1), 'b': affine(2, 1), 'd': affine(1, 0),
             'e': affine(2, 0), 'f': affine(2, 0), 'g': affine(2, 0)}),
        'lemma-3.15-T-without-dynamic-rules-reversed': (
            no_dyn,
            {'a': affine(1, 1), 'b': affine(1, 1), 'c': affine(1, 1),
             'e': affine(4, 0), 'f': affine(4, 0), 'g': affine(4, 0)}),
    }
    out = []
    for name, (rules, interp) in cases.items():
        problem = systems.reversed_strict(rules)
        cert = {'problem': name + '.srs', 'steps': [{
            'type': 'natural', 'dimension': 1, 'interpretation': interp,
            'removed': [line.strip() for line in problem.splitlines()]}],
            'source': 'interpretation given in the proof of Lemma 3.15 of the paper'}
        with open(os.path.join(PROBLEMS, name + '.srs'), 'w') as f:
            f.write(problem)
        with open(os.path.join(RESULTS, name + '.json'), 'w') as f:
            json.dump(cert, f, indent=1)
            f.write('\n')
        try:
            check(problem, cert)
            verdict = 'accepted'
        except CertificateError as e:
            verdict = f'REJECTED: {e}'
        out.append((name, len(rules), verdict))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--timeout', type=int, default=1800, help='seconds per problem')
    ap.add_argument('numbers', nargs='*', type=int)
    args = ap.parse_args()
    todo = args.numbers or list(range(1, 12))
    os.makedirs(PROBLEMS, exist_ok=True)
    os.makedirs(RESULTS, exist_ok=True)

    rows = []
    for k in todo:
        name = f'collatz-T-{k:02d}'
        problem = systems.subsystem_problem(k)
        problem_file = os.path.join(PROBLEMS, name + '.srs')
        with open(problem_file, 'w') as f:
            f.write(problem)
        with open(os.path.join(UPSTREAM, 'relative', name + '.srs')) as f:
            same = rule_set(f.read()) == rule_set(problem)

        kind, dim, width = PUBLISHED[k]
        cert_file = os.path.join(RESULTS, name + '.json')
        cmd = [sys.executable, os.path.join(HERE, 'run_published.py'), problem_file, cert_file,
               '-i', kind, '-d', str(dim), '-rw', str(width), '-any', '--no-print']
        start = time.time()
        try:
            run = subprocess.run(cmd, capture_output=True, text=True, timeout=args.timeout)
            found = run.returncode == 0
            note = '' if found else (run.stderr.strip().splitlines() or ['failed'])[-1]
        except subprocess.TimeoutExpired:
            found, note = False, f'no result within {args.timeout} s'
        seconds = time.time() - start

        steps, verdict = '-', 'not checked'
        if found:
            with open(cert_file) as f:
                cert = json.load(f)
            try:
                result = check(problem, cert)
                steps = len(result['steps'])
                verdict = 'accepted'
            except CertificateError as e:
                verdict = f'REJECTED: {e}'
        row = (k, paper(systems.T[k - 1]), kind, dim, width, same, found, seconds, steps,
               verdict, note)
        rows.append(row)
        print(f'{name}: same problem as published={same}  found={found}  '
              f'{seconds:.1f} s  steps={steps}  checker: {verdict} {note}', flush=True)

    lemma = lemma_3_15()
    for name, n, verdict in lemma:
        print(f'{name}: {n} rules, checker: {verdict}', flush=True)

    with open(os.path.join(RESULTS, 'summary.md'), 'w') as f:
        f.write('# Phase 0 results\n\n'
                'Each row is the Collatz system T with one rule left out. "Found" means the\n'
                'published prover, driven by the python-sat build of CaDiCaL, found a proof with\n'
                'the published search parameters. "Checker" is the verdict of `checker/check.py`\n'
                'on the certificate saved next to this file.\n\n'
                '| # | Rule left out | Type | Dimension | Coefficient values | Same problem as '
                'published | Found | Seconds | Steps | Checker |\n'
                '|---|---|---|---|---|---|---|---|---|---|\n')
        for k, rule, kind, dim, width, same, found, seconds, steps, verdict, note in rows:
            f.write(f'| {k} | `{rule}` | {kind} | {dim} | {width} | {"yes" if same else "NO"} | '
                    f'{"yes" if found else "no: " + note} | {seconds:.1f} | {steps} | '
                    f'{verdict} |\n')
        f.write('\nLemma 3.15 of the paper (hand-written interpretations, reversed systems):\n\n'
                '| Statement | Rules | Checker |\n|---|---|---|\n')
        for name, n, verdict in lemma:
            f.write(f'| `{name}` | {n} | {verdict} |\n')
    ok = all(r[5] and r[6] and r[9] == 'accepted' for r in rows) and \
        all(v == 'accepted' for _, _, v in lemma)
    print('ALL ACCEPTED' if ok else 'SOME PROBLEMS NOT REPRODUCED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
