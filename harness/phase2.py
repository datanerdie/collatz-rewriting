#!/usr/bin/env python3
"""Phase 2: block-accelerated systems, tested against direct iteration of the map.

For a block size k, the two single-step dynamic rules of a system are replaced by 2^k block
rules, one for each choice of the last k binary digits, each applying k steps of the map at
once (harness/systems.py, `accelerate`).  The written argument is in
docs/phase2-block-acceleration.md.  This script checks, for the paper's system T and the
shifted system S and every block size:

  1. Shape and arithmetic: every block rule is exactly k steps of the map, as an identity of
     affine functions.
  2. Derivability: every block rule is a rewrite sequence of single-step rules, so the
     accelerated system can do nothing the single-step system cannot.
  3. The termination lemma for the system without its left-end rules (checked certificate).
  4. Exhaustive simulation and long random runs, as in Phase 1.
  5. For the siblings with extra cycles: whether the accelerated sibling still has a loop.

Usage:  phase2.py [--blocks 2 3 4 5 6] [--numbers N] [--digits K] [--length L] [--jobs J]
"""
import argparse
import os
import random
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

import systems as sy                                                    # noqa: E402
from checks import (Failure, TooLarge, LIMIT, check_rules, explore,     # noqa: E402
                    find_loop, lemma_certificates, need, random_run, simulate)

PROBLEMS = os.path.join(ROOT, 'problems', 'phase2')
RESULTS = os.path.join(ROOT, 'results', 'phase2')

# Members of the known extra cycles of the sibling maps.
CYCLES = {
    'T-': [5, 7, 10, 17, 25, 37, 55, 82, 41, 61, 91, 136, 68, 34],
    'S-': [4, 6, 9, 16, 24, 36, 54, 81, 40, 60, 90, 135, 67, 33],
    'T5': [13, 33, 83, 208, 104, 52, 26, 17, 43, 108, 54, 27, 68, 34],
}
SIBLINGS = {'T-': sy.THREE_N_MINUS_ONE, 'S-': sy.SHIFTED_THREE_N_MINUS_ONE,
            'T5': sy.FIVE_N_PLUS_ONE}


def check_derivable(system):
    """Every block rule is a rewrite sequence of the single-step rules in `system.unit`."""
    for l, r in system.dynamic:
        need(r in explore(l, system.unit), f'{system.name}: {l} -> {r} is not derivable')


def shrinking(system):
    """How many block rules multiply by less than they divide: 3^j < 2^k."""
    return sum(sy.affine(r)[0] < sy.affine(l)[0] for l, r in system.dynamic)


def work(job):
    """Everything for one accelerated system; runs in a worker process."""
    base_name, k, numbers, digits, length, bits, runs = job
    base = {'T': sy.COLLATZ, 'S': sy.SHIFTED}[base_name]
    system = sy.accelerate(base, k)
    start = time.time()
    try:
        n_rules = check_rules(system)
        check_derivable(system)
        (lemma, lemma_rules), = lemma_certificates(system, PROBLEMS, RESULTS, which=('left',))
        # The search problem for Phase 3: left-end rules strict at the left end, the rest weak.
        with open(os.path.join(PROBLEMS, system.name + '.srs'), 'w') as f:
            f.write(system.problem(strict=system.left, top=True))
        a, b, c = simulate(system, numbers, digits, length)
        rng = random.Random(1000 * k + len(base_name))
        rand = [random_run(system, rng.getrandbits(bits) | 1 << (bits - 1), rng)
                for _ in range(runs)]
    except Failure as e:
        return {'name': system.name, 'error': str(e)}
    except TooLarge as e:
        return {'name': system.name, 'error': f'rewrite graph from {e} exceeds {LIMIT:,}'}
    return {'name': system.name, 'base': base_name, 'k': k, 'rules': n_rules,
            'symbols': len(system.symbols), 'shrinking': shrinking(system),
            'lemma': lemma, 'lemma_rules': lemma_rules, 'lowest': system.lowest,
            'sim': [(st.starts, st.strings, st.largest, st.longest) for st in (a, b, c)],
            'dyn': (min(r[0] for r in rand), max(r[0] for r in rand)),
            'tot': (min(r[1] for r in rand), max(r[1] for r in rand)),
            'seconds': time.time() - start,
            'example': [sy.pretty_rule(r) for r in system.dynamic] if k <= 3 else None}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--blocks', type=int, nargs='+', default=[2, 3, 4, 5, 6])
    ap.add_argument('--numbers', type=int, default=1000)
    ap.add_argument('--digits', type=int, default=5)
    ap.add_argument('--length', type=int, default=4)
    ap.add_argument('--random-bits', type=int, default=64)
    ap.add_argument('--random-runs', type=int, default=20)
    ap.add_argument('--jobs', type=int, default=os.cpu_count() or 1)
    ap.add_argument('--out', default=os.path.join(RESULTS, 'summary.md'))
    args = ap.parse_args()
    os.makedirs(PROBLEMS, exist_ok=True)
    os.makedirs(RESULTS, exist_ok=True)
    out = []
    say = lambda line='': (print(line, flush=True), out.append(line))

    # The equivalence argument needs every start value below 2^k to be convergent.
    top = 2 ** max(args.blocks)
    for n in range(1, top):
        v, steps = n, 0
        while v != 1:
            v = sy.COLLATZ.apply_map(v)
            steps += 1
            need(steps < 10000, f'{n} did not reach 1')

    jobs = [(base, k, args.numbers, args.digits, args.length, args.random_bits,
             args.random_runs) for k in args.blocks for base in ('T', 'S')]
    with Pool(args.jobs) as pool:
        results = pool.map(work, jobs, chunksize=1)
    for r in results:
        if 'error' in r:
            raise Failure(f'{r["name"]}: {r["error"]}')

    say('# Phase 2 results')
    say()
    say('Produced by `harness/phase2.py`. The argument these checks support is in')
    say('`docs/phase2-block-acceleration.md`. `T.k3` is the paper\'s system T in blocks of 3')
    say('steps; `S.k3` is the shifted system S in blocks of 3 steps.')
    say()
    say(f'Every start value below {top} reaches 1 under the Collatz map (checked directly); the')
    say('equivalence argument for block size k needs this below 2^k.')

    say()
    say('## Block rules')
    say()
    say('"Arithmetic" means each block rule equals k steps of the map as an exact identity of')
    say('affine functions. "Derivable" means each block rule is a rewrite sequence of')
    say('single-step rules. "Shrinking blocks" counts the block rules that multiply by a')
    say('smaller power of 3 than the power of 2 they divide by.')
    say()
    say('| System | Block size | Symbols | Rules | Block rules | Shrinking blocks | Arithmetic | '
        'Derivable |')
    say('|---|---|---|---|---|---|---|---|')
    for r in results:
        blocks = 2 ** r['k']
        say(f'| {r["name"]} | {r["k"]} | {r["symbols"]} | {r["rules"]} | {blocks} | '
            f'{r["shrinking"]} ({100 * r["shrinking"] / blocks:.1f}%) | all hold | all |')
    say()
    say('The block rules for the two smallest block sizes:')
    say()
    for r in results:
        if r['example']:
            say(f'- **{r["name"]}:** ' + ', '.join(f'`{x}`' for x in r['example']))

    say()
    say('## Termination lemma')
    say()
    say('Each accelerated system without its left-end rules terminates: one-dimensional natural')
    say('interpretations on the reversed systems, verified by `checker/check.py`. (Without its')
    say('block rules an accelerated system is its base system without dynamic rules, covered')
    say('in Phases 0 and 1.)')
    say()
    say('| Statement | Rules | Checker |')
    say('|---|---|---|')
    for r in results:
        say(f'| `{r["lemma"]}` | {r["lemma_rules"]} | accepted |')

    say()
    say('## Exhaustive simulation')
    say()
    say('The complete rewrite graph from each start string: every rule at every position of')
    say('every reachable string. In the first two kinds of row, every block step must equal k')
    say('steps of the map, the graph must have no cycle, and rewriting may stop only at the')
    say('plain binary string of a value below 2^k.')
    say()
    say('| System | Start strings | How many | Strings visited | Largest graph | '
        'Longest rewrite sequence | Result |')
    say('|---|---|---|---|---|---|---|')
    for r in results:
        labels = [f'binary strings of {r["lowest"]}..{args.numbers}',
                  f'all canonical strings with up to {args.digits} digits',
                  f'all strings of length 1..{args.length} over the whole alphabet']
        for label, (starts, strings, largest, longest) in zip(labels, r['sim']):
            verdict = 'no cycle' if label.startswith('all strings') else 'passed'
            say(f'| {r["name"]} | {label} | {starts:,} | {strings:,} | {largest:,} | '
                f'{longest:,} | {verdict} |')

    say()
    say('## Long random runs')
    say()
    say(f'{args.random_runs} random {args.random_bits}-bit numbers per system, rules chosen '
        'uniformly at random among all')
    say('applicable ones until none applies. The number of block steps must equal the number')
    say('of k-step jumps the map itself needs to fall below 2^k.')
    say()
    say('| System | Runs | Block steps (min–max) | Rewrite steps (min–max) | Result |')
    say('|---|---|---|---|---|')
    for r in results:
        say(f'| {r["name"]} | {args.random_runs} | {r["dyn"][0]}–{r["dyn"][1]} | '
            f'{r["tot"][0]:,}–{r["tot"][1]:,} | all agree with the map |')

    say()
    say('## Accelerated siblings')
    say()
    say('An accelerated system stops as soon as a value below 2^k appears at a multiple of k')
    say('steps, so a cycle of the map survives acceleration only if it avoids such values.')
    say('For each sibling and block size the table gives a start value on a known cycle from')
    say('which the accelerated system has a loop (found by search and replayed), or "none" if')
    say('no member of the known cycles gives one.')
    say()
    say('| Sibling | ' + ' | '.join(f'k = {k}' for k in args.blocks) + ' |')
    say('|---|' + '---|' * len(args.blocks))
    for name, base in SIBLINGS.items():
        cells = []
        for k in args.blocks:
            system = sy.accelerate(base, k)
            check_rules(system)
            check_derivable(system)
            found = None
            for n in CYCLES[name]:
                loop = find_loop(system, n) if n >= 2 ** k else None
                if loop:
                    found = f'loop from {n} ({len(loop) - 1} rewrite steps)'
                    break
            cells.append(found or 'none')
        say(f'| {name}: {base.title} | ' + ' | '.join(cells) + ' |')

    with open(args.out, 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    try:
        main()
    except Failure as e:
        print(f'FAILED: {e}')
        sys.exit(1)
