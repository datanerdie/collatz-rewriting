#!/usr/bin/env python3
"""Phase 1: check the shifted systems against the map they are meant to simulate.

The written argument is in docs/phase1-shifted-system.md.  This script machine-checks the
parts of it that are finite:

  1. Shape: every rule is a dynamic rule `u|> -> v|>`, a left-end rule, or an inner rule.
  2. Arithmetic: inner and left-end rules do not change the value of a string, and dynamic
     rules apply exactly one step of the map.  Checked exactly, as identities of affine maps.
  3. Two termination lemmas (the system without its left-end rules, and without its dynamic
     rules), by hand-written interpretations verified with checker/check.py.
  4. Exhaustive simulation: the complete rewrite graph (every rule at every position) from
       a. the binary string of every number up to a bound,
       b. every canonical string with at most a given number of digits,
       c. every string at all over the alphabet up to a given length.
     In (a) and (b) every step must follow the map, the graph must be finite and free of
     cycles, and every string where rewriting stops must be the plain binary string of a stop
     value.  In (c) the graph must be finite and free of cycles.
  5. Long random runs on large numbers.
  6. Siblings with extra cycles (3n-1 and 5n+1): an explicit looping rewrite sequence.

Usage:  phase1.py [--numbers N] [--digits K] [--length L]
"""
import argparse
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'checker'))

import systems as sy                                              # noqa: E402
from checks import (Failure, TooLarge, LIMIT, check_rules, find_loop,   # noqa: E402
                    lemma_certificates, random_run, simulate)

PROBLEMS = os.path.join(ROOT, 'problems', 'phase1')
RESULTS = os.path.join(ROOT, 'results', 'phase1')


# ---------------------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--numbers', type=int, default=1000)
    ap.add_argument('--digits', type=int, default=6)
    ap.add_argument('--length', type=int, default=5)
    ap.add_argument('--random-bits', type=int, default=64)
    ap.add_argument('--random-runs', type=int, default=20)
    ap.add_argument('--out', default=os.path.join(RESULTS, 'summary.md'))
    args = ap.parse_args()
    os.makedirs(PROBLEMS, exist_ok=True)
    os.makedirs(RESULTS, exist_ok=True)
    out = []
    say = lambda line='': (print(line, flush=True), out.append(line))

    say('# Phase 1 results')
    say()
    say('Produced by `harness/phase1.py`. The argument these checks support is in')
    say('`docs/phase1-shifted-system.md`.')

    say()
    say('## Rules')
    say()
    say('Every rule has one of the three allowed shapes; inner and left-end rules leave the')
    say('value of a string unchanged; dynamic rules apply exactly one step of the map. These')
    say('are exact identities between affine functions, not samples.')
    say()
    say('| System | Simulates | Symbols | Rules | Shape and arithmetic |')
    say('|---|---|---|---|---|')
    for system in sy.SYSTEMS:
        n = check_rules(system)
        say(f'| {system.name} | {system.title} | {len(system.symbols)} | {n} | all hold |')

    say()
    say('## Termination lemmas')
    say()
    say('One-dimensional natural interpretations on the reversed systems, verified by')
    say('`checker/check.py`. Certificates are next to this file.')
    say()
    say('| Statement | Rules | Checker |')
    say('|---|---|---|')
    for system in (sy.SHIFTED, sy.SHIFTED_TWO_MARKERS):
        for name, n in lemma_certificates(system, PROBLEMS, RESULTS):
            say(f'| `{name}` | {n} | accepted |')

    say()
    say('## Exhaustive simulation')
    say()
    say('For each start string the complete rewrite graph was built: every rule at every')
    say('position of every reachable string. "Strings" counts graph nodes summed over all')
    say('start strings.')
    say()
    say('| System | Start strings | How many | Strings visited | Largest graph | '
        'Longest rewrite sequence | Result |')
    say('|---|---|---|---|---|---|---|')
    for system in (sy.COLLATZ, sy.SHIFTED, sy.SHIFTED_TWO_MARKERS):
        start = time.time()
        a, b, c = simulate(system, args.numbers, args.digits, args.length)
        rows = [(f'binary strings of {system.lowest}..{args.numbers}', a,
                 'follows the map, no cycle, stops only at a stop value'),
                (f'all canonical strings with up to {args.digits} digits', b,
                 'follows the map, no cycle, stops only at a stop value'),
                (f'all strings of length 1..{args.length} over the whole alphabet', c,
                 'no cycle')]
        for label, st, result in rows:
            say(f'| {system.name} | {label} | {st.starts:,} | {st.strings:,} | '
                f'{st.largest:,} | {st.longest:,} | {result} |')
        print(f'  ({system.name}: {time.time() - start:.0f} s)', flush=True)

    say()
    say('## Long random runs')
    say()
    say(f'{args.random_runs} random {args.random_bits}-bit numbers per system, rules chosen '
        'uniformly at random among all')
    say('applicable ones until none applies. The number of dynamic steps must equal the number')
    say('of steps the map itself takes to reach a stop value.')
    say()
    say('| System | Runs | Dynamic steps (min–max) | Rewrite steps (min–max) | Result |')
    say('|---|---|---|---|---|')
    rng = random.Random(2026)
    for system in (sy.COLLATZ, sy.SHIFTED, sy.SHIFTED_TWO_MARKERS):
        runs = [random_run(system, rng.getrandbits(args.random_bits) | 1 << (args.random_bits - 1),
                           rng) for _ in range(args.random_runs)]
        d, t = [r[0] for r in runs], [r[1] for r in runs]
        say(f'| {system.name} | {len(runs)} | {min(d)}–{max(d)} | {min(t):,}–{max(t):,} | '
            'all agree with the map |')

    say()
    say('## Siblings loop')
    say()
    say('Each sibling has a rewrite sequence that returns to its own start string, so it does')
    say('not terminate. The sequences were found by search and replayed step by step. Each')
    say('starts and ends at the binary string of the number in the "Start" column.')
    say()
    say('| System | Simulates | Start | Loop |')
    say('|---|---|---|---|')
    for system, n in ((sy.THREE_N_MINUS_ONE, 5), (sy.THREE_N_MINUS_ONE, 17),
                      (sy.SHIFTED_THREE_N_MINUS_ONE, 4), (sy.SHIFTED_THREE_N_MINUS_ONE, 16),
                      (sy.FIVE_N_PLUS_ONE, 13), (sy.FIVE_N_PLUS_ONE, 17)):
        loop = find_loop(system, n)
        if loop is None:
            raise Failure(f'{system.name}: no loop found from {n}')
        shown = ' → '.join(sy.pretty(s) for s in loop)
        if len(loop) > 12:
            shown = ' → '.join(sy.pretty(s) for s in loop[:4]) + \
                f' → … ({len(loop) - 1} steps) … → ' + sy.pretty(loop[-1])
        say(f'| {system.name} | {system.title} | {n} | {shown} |')

    with open(args.out, 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('ALL CHECKS PASSED')


if __name__ == '__main__':
    try:
        main()
    except Failure as e:
        print(f'FAILED: {e}')
        sys.exit(1)
    except TooLarge as e:
        print(f'FAILED: the rewrite graph from {e} exceeds {LIMIT:,} strings')
        sys.exit(1)
