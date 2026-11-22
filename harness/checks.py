"""Checks shared by the phase scripts: rule arithmetic, termination lemmas, simulation.

Everything here compares a rewriting system with the map on numbers it is meant to simulate
(see harness/systems.py).  A failed check raises `Failure`.
"""
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'checker'))

import systems as sy                                                 # noqa: E402
from check import CertificateError, check                           # noqa: E402
import rewrite                                                      # noqa: E402
from rewrite import TooLarge, find_cycle, longest_path, successors  # noqa: E402,F401

LIMIT = 3000000         # largest rewrite graph that will be built for one start string


def explore(start, rules, limit=None):
    return rewrite.explore(start, rules, limit or LIMIT)


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
        need(A % 2 ** system.power == 0, f'{system.name}: {l}->{r} does not fix the parities')
        need(sy.iterate_affine(system.step, A, B, system.power) == sy.affine(r),
             f'{system.name}: {l}->{r} is not {system.power} step(s) of the map')
    return len(system.rules)


# ---------------------------------------------------------------------------------------
# 3: the two termination lemmas
# ---------------------------------------------------------------------------------------

def lemma_certificates(system, problems, results, which=('left', 'dynamic')):
    """SN(system without left-end rules) and/or SN(system without dynamic rules).

    One-dimensional natural interpretations on the reversed system, written to `problems` and
    `results` and verified with checker/check.py.
    """
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
        if label.split('-')[1] not in which:
            continue
        name = f'{system.name}-{label}-reversed'
        problem = sy.reversed_strict(rules)
        used = {s for l, r in rules for s in l + r}
        cert = {'problem': name + '.srs', 'steps': [{
            'type': 'natural', 'dimension': 1,
            'interpretation': {s: m for s, m in interp.items() if s in used},
            'removed': [line.strip() for line in problem.splitlines()]}]}
        with open(os.path.join(problems, name + '.srs'), 'w') as f:
            f.write(problem)
        with open(os.path.join(results, name + '.json'), 'w') as f:
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
    a, b, c = Stats(), Stats(), Stats()
    for n in range(system.lowest, numbers + 1):
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
    """A shortest rewrite sequence from the binary string of n back to itself, or None."""
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
    if last is None:
        return None
    loop = [start]
    while last != start:
        loop.append(last)
        last = parent[last]
    loop = [start] + loop[:0:-1] + [start]
    for s, t in zip(loop, loop[1:]):                # replay it
        need(any(u == t for _, _, u in successors(s, system.rules)),
             f'{system.name}: {s} -> {t} is not a rewrite step')
    return loop
