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
import itertools
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'checker'))

import systems as sy                                              # noqa: E402
from check import CertificateError, check                        # noqa: E402
import rewrite                                                   # noqa: E402
from rewrite import TooLarge, find_cycle, longest_path, successors  # noqa: E402

LIMIT = 3000000         # largest rewrite graph that will be built for one start string


def explore(start, rules, limit=None):
    return rewrite.explore(start, rules, limit or LIMIT)

PROBLEMS = os.path.join(ROOT, 'problems', 'phase1')
RESULTS = os.path.join(ROOT, 'results', 'phase1')


class Failure(Exception):
    pass


def need(condition, message):
    if not condition:
        raise Failure(message)


# ---------------------------------------------------------------------------------------
# 1 and 2: shape and arithmetic of the rules
# ---------------------------------------------------------------------------------------

def check_rules(system):
    digits = set(system.digits)
    for l, r in system.inner:
        need(set(l + r) <= digits, f'{system.name}: inner rule {l}->{r} contains a marker')
        need(sy.affine(l) == sy.affine(r), f'{system.name}: {l}->{r} changes the value')
    for l, r in system.left:
        need(l[0] in sy.LEFT_MARKERS and r[0] in sy.LEFT_MARKERS and
             set(l[1:] + r[1:]) <= digits, f'{system.name}: bad left-end rule {l}->{r}')
        need(sy.affine(l) == sy.affine(r), f'{system.name}: {l}->{r} changes the value')
    for l, r in system.dynamic:
        need(l[-1] == r[-1] == sy.RIGHT_MARKER and set(l[:-1] + r[:-1]) <= digits,
             f'{system.name}: bad dynamic rule {l}->{r}')
        A, B = sy.affine(l)                 # the value before the step is A*x + B
        need(A % 2 == 0, f'{system.name}: {l}->{r} does not fix the parity')
        p, q = system.step[B % 2]           # the map sends it to (p*(A*x + B) + q) / 2
        need((p * A) % 2 == 0 and (p * B + q) % 2 == 0, f'{system.name}: {l}->{r} not integral')
        need(((p * A) // 2, (p * B + q) // 2) == sy.affine(r),
             f'{system.name}: {l}->{r} is not one step of the map')
    return len(system.rules)


# ---------------------------------------------------------------------------------------
# 3: the two termination lemmas
# ---------------------------------------------------------------------------------------

def lemma_certificates(system):
    """SN(system without left-end rules) and SN(system without dynamic rules)."""
    lin = lambda m, c: {'M': [[m]], 'v': [c]}
    ternary = [s for s in system.symbols if s in 'efg']
    cases = {
        'without-left-end-rules': (
            system.dynamic + system.inner,
            {**{s: lin(2, 1) for s in 'ab'}, 'd': lin(1, 0), 'i': lin(2, 0),
             **{s: lin(2, 0) for s in ternary}}),
        'without-dynamic-rules': (
            system.inner + system.left,
            {**{s: lin(1, 1) for s in 'ab' + ''.join(system.markers)}, 'i': lin(2, 1),
             **{s: lin(4, 0) for s in ternary}}),
    }
    out = []
    for label, (rules, interp) in cases.items():
        name = f'{system.name}-{label}-reversed'
        problem = sy.reversed_strict(rules)
        used = {s for l, r in rules for s in l + r}
        cert = {'problem': name + '.srs', 'steps': [{
            'type': 'natural', 'dimension': 1,
            'interpretation': {s: m for s, m in interp.items() if s in used},
            'removed': [line.strip() for line in problem.splitlines()]}]}
        with open(os.path.join(PROBLEMS, name + '.srs'), 'w') as f:
            f.write(problem)
        with open(os.path.join(RESULTS, name + '.json'), 'w') as f:
            json.dump(cert, f, indent=1)
            f.write('\n')
        try:
            check(problem, cert)
        except CertificateError as e:
            raise Failure(f'{name}: certificate rejected: {e}')
        out.append((name, len(rules)))
    return out


# ---------------------------------------------------------------------------------------
# 4: exhaustive simulation
# ---------------------------------------------------------------------------------------

class Stats:
    def __init__(self):
        self.starts = self.strings = self.largest = self.longest = 0

    def add(self, graph):
        self.starts += 1
        self.strings += len(graph)
        self.largest = max(self.largest, len(graph))
        self.longest = max(self.longest, longest_path(graph))


def check_canonical_graph(system, start, stats):
    """All rewrite sequences from a canonical string follow the map and end at a stop value."""
    graph = explore(start, system.rules)
    cycle = find_cycle(graph)
    need(cycle is None, f'{system.name}: cycle from {start}: {cycle}')
    dynamic = set(system.dynamic)
    binary = set(sy.BINARY)
    for s, edges in graph.items():
        v = sy.value(s)
        for rule, t in edges:
            if rule in dynamic:
                need(v not in system.stop, f'{system.name}: dynamic step at stop value: {s}')
                need(sy.value(t) == system.apply_map(v), f'{system.name}: wrong step {s}->{t}')
            else:
                need(sy.value(t) == v, f'{system.name}: value changed {s}->{t}')
        if not edges:
            # Rewriting stops only at a plain binary string of a stop value.  (The value 1 is
            # outside the domain m >= 2 of the shifted map and is the bare string `cd`.)
            need(set(s[1:-1]) <= binary, f'{system.name}: stuck at non-binary string {s}')
            need(v in system.stop or s == 'cd', f'{system.name}: stuck at {s} (value {v})')
    stats.add(graph)


def check_any_graph(system, start, stats):
    graph = explore(start, system.rules)
    cycle = find_cycle(graph)
    need(cycle is None, f'{system.name}: cycle from {start}: {cycle}')
    stats.add(graph)


def simulate(system, numbers, digits, length):
    lowest = 2 if system.name.startswith('S') else 1
    a, b, c = Stats(), Stats(), Stats()
    for n in range(lowest, numbers + 1):
        check_canonical_graph(system, system.encode(n), a)
    for k in range(digits + 1):
        for marker in system.markers:
            for body in itertools.product(system.digits, repeat=k):
                check_canonical_graph(system, marker + ''.join(body) + sy.RIGHT_MARKER, b)
    for k in range(1, length + 1):
        for body in itertools.product(system.symbols, repeat=k):
            check_any_graph(system, ''.join(body), c)
    return a, b, c


# ---------------------------------------------------------------------------------------
# 5: long random runs
# ---------------------------------------------------------------------------------------

def random_run(system, n, rng):
    """Apply randomly chosen rules until none applies; return the number of dynamic steps."""
    expected, v = 0, n
    while v not in system.stop:
        v = system.apply_map(v)
        expected += 1
    dynamic = set(system.dynamic)
    s, steps, total = system.encode(n), 0, 0
    while True:
        moves = successors(s, system.rules)
        if not moves:
            break
        rule, _, s = rng.choice(moves)
        steps += rule in dynamic
        total += 1
    need(sy.value(s) in system.stop and set(s[1:-1]) <= set(sy.BINARY),
         f'{system.name}: random run from {n} stopped at {s}')
    need(steps == expected, f'{system.name}: {steps} dynamic steps from {n}, expected {expected}')
    return steps, total


# ---------------------------------------------------------------------------------------
# 6: siblings must loop
# ---------------------------------------------------------------------------------------

def find_loop(system, n):
    """A shortest rewrite sequence from the binary string of n back to itself."""
    start = system.encode(n)
    graph = explore(start, system.rules, limit=20000)
    parent, frontier, last = {}, [start], None
    while frontier and last is None:                # breadth-first search for a way back
        following = []
        for s in frontier:
            for _, t in graph[s]:
                if t == start:
                    last = s
                    break
                if t not in parent:
                    parent[t] = s
                    following.append(t)
            if last is not None:
                break
        frontier = following
    need(last is not None, f'{system.name}: no loop found from {n}')
    loop = [start]
    while last != start:
        loop.append(last)
        last = parent[last]
    loop = [start] + loop[:0:-1] + [start]
    for s, t in zip(loop, loop[1:]):                # replay it
        need(any(u == t for _, _, u in successors(s, system.rules)),
             f'{system.name}: {s} -> {t} is not a rewrite step')
    return loop


# ---------------------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--numbers', type=int, default=1000)
    ap.add_argument('--digits', type=int, default=6)
    ap.add_argument('--length', type=int, default=5)
    ap.add_argument('--random-bits', type=int, default=64)
    ap.add_argument('--random-runs', type=int, default=20)
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
        for name, n in lemma_certificates(system):
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
        lowest = 2 if system.name.startswith('S') else 1
        rows = [(f'binary strings of {lowest}..{args.numbers}', a,
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
        shown = ' → '.join(sy.pretty(s) for s in loop)
        if len(loop) > 12:
            shown = ' → '.join(sy.pretty(s) for s in loop[:4]) + \
                f' → … ({len(loop) - 1} steps) … → ' + sy.pretty(loop[-1])
        say(f'| {system.name} | {system.title} | {n} | {shown} |')

    with open(os.path.join(RESULTS, 'summary.md'), 'w') as f:
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
