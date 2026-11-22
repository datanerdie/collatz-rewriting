#!/usr/bin/env python3
"""Tests for checker/check.py.  Run with:  python3 tests/test_checker.py

Symbols follow the published problem files: a = f (x -> 2x), b = t (x -> 2x+1),
c = left end marker, d = right end marker, e, f, g = ternary digits 0, 1, 2.
"""
import copy
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'checker'))
from check import CertificateError, check, compose, interpret, parse_problem, Natural  # noqa: E402

# The Collatz system T with the rule  t> -> 2>  left out: the three left-end rules are
# top-terminating relative to the rest (problem "collatz-T-02" of Yolcu, Aaronson & Heule).
T02 = """
ad ->= d
ae ->= ea
af ->= eb
ag ->= fa
be ->= fb
bf ->= ga
bg ->= gb
ce |-> cb
cf |-> caa
cg |-> cab
"""

# Their published one-dimensional proof, transcribed by hand from proofs/collatz-T-02.log:
# binary digits and the left marker are x -> x, everything else is x -> x + 1.
T02_CERT = {'steps': [{
    'type': 'natural', 'dimension': 1,
    'interpretation': {s: {'M': [[1]], 'v': [0 if s in 'abc' else 1]} for s in 'abcdefg'},
    'removed': ['ce |-> cb', 'cf |-> caa', 'cg |-> cab'],
}]}

# Example 2.16 of the paper: SN(aa -> aba / b -> bb), a two-dimensional natural proof.
EX216 = "aa -> aba\nb ->= bb\n"
EX216_CERT = {'steps': [{
    'type': 'natural', 'dimension': 2,
    'interpretation': {'a': {'M': [[1, 1], [0, 0]], 'v': [0, 1]},
                       'b': {'M': [[1, 0], [0, 0]], 'v': [0, 0]}},
    'removed': ['aa -> aba'],
}]}

# A small arctic example: a -> b is removed because every entry drops (or stays -infinity).
ARCTIC = "a -> b\n"
ARCTIC_CERT = {'steps': [{
    'type': 'arctic', 'dimension': 2,
    'interpretation': {'a': {'M': [[1, None], [2, 3]], 'v': [None, None]},
                       'b': {'M': [[0, None], [1, 2]], 'v': [None, None]}},
    'removed': ['a -> b'],
}]}


def rejected(problem, cert):
    try:
        check(problem, cert)
    except CertificateError:
        return True
    return False


def test_accepts_valid():
    assert check(T02, T02_CERT)['kind'] == 'relative top termination'
    assert check(EX216, EX216_CERT)['kind'] == 'relative termination'
    assert check(ARCTIC, ARCTIC_CERT)['kind'] == 'relative termination'


def test_rejects_every_single_entry_decrease():
    """Lowering the constant of any ternary digit in the T-02 proof must break it.

    (Lowering [d] alone does not: with d = x the proof is still valid.)
    """
    for sym in 'efg':
        bad = copy.deepcopy(T02_CERT)
        bad['steps'][0]['interpretation'][sym]['v'] = [0]
        assert rejected(T02, bad), sym


def test_rejects_wrong_claims():
    bad = copy.deepcopy(T02_CERT)
    bad['steps'][0]['removed'] = ['ce |-> cb']                 # two strict rules left over
    assert rejected(T02, bad)
    partial = check(T02, bad, allow_partial=True)              # ... unless partial is allowed
    assert partial['remaining_strict'] == ['cf |-> caa', 'cg |-> cab']

    bad = copy.deepcopy(T02_CERT)
    bad['steps'][0]['removed'].append('ad ->= d')              # weak rules cannot be removed
    assert rejected(T02, bad)

    bad = copy.deepcopy(T02_CERT)
    del bad['steps'][0]['interpretation']['g']                 # missing symbol
    assert rejected(T02, bad)

    bad = copy.deepcopy(T02_CERT)
    bad['steps'][0]['interpretation']['a']['M'] = [[-1]]       # not a natural number
    assert rejected(T02, bad)

    bad = copy.deepcopy(EX216_CERT)
    bad['steps'][0]['interpretation']['b']['M'][0][0] = 0      # no longer strictly monotone
    assert rejected(EX216, bad)

    bad = copy.deepcopy(ARCTIC_CERT)
    bad['steps'][0]['interpretation']['b']['M'][1][1] = 3      # 3 >> 3 is false
    assert rejected(ARCTIC, bad)

    bad = copy.deepcopy(ARCTIC_CERT)
    bad['steps'][0]['interpretation']['a']['v'] = [0, None]    # constants not allowed here
    assert rejected(ARCTIC, bad)


def test_rejects_the_full_collatz_system_with_this_interpretation():
    """Putting the left-out rule back must make the same interpretation fail: t> -> 2> grows."""
    full = T02 + "bd ->= gd\n"
    assert rejected(full, T02_CERT)


def test_values_really_decrease_along_rewrites():
    """Independent of the entrywise test: replay random rewrite sequences and watch the value.

    For an accepted natural certificate the first coordinate of [string](x) must never go up,
    and must go down at every use of a removed rule at the left end.
    """
    rules, _ = parse_problem(T02)
    step = T02_CERT['steps'][0]
    interp = {s: (e['M'], e['v']) for s, e in step['interpretation'].items()}
    rng = random.Random(0)
    x0 = [3]
    value = lambda w: [sum(m * x for m, x in zip(row, x0)) + c
                       for row, c in zip(*interpret(Natural, w, interp))]
    strict_uses = 0
    for _ in range(300):
        w = ('c',) + tuple(rng.choice('abefg') for _ in range(rng.randint(1, 14))) + ('d',)
        for _ in range(400):
            moves = [(i, r) for r in rules for i in range(len(w) - len(r.left) + 1)
                     if w[i:i + len(r.left)] == r.left and (i == 0 or not r.top)]
            if not moves:
                break
            i, r = rng.choice(moves)
            before = value(w)
            w = w[:i] + r.right + w[i + len(r.left):]
            after = value(w)
            assert after[0] <= before[0], (r, w)
            if r.top:
                assert after[0] < before[0], (r, w)
                strict_uses += 1
    assert strict_uses > 100


def test_compose_matches_function_composition():
    f = ([[2, 1], [0, 3]], [1, 0])
    g = ([[1, 4], [2, 0]], [5, 6])
    M, v = compose(Natural, f, g)
    x = [7, 11]
    apply = lambda h, y: [sum(m * t for m, t in zip(row, y)) + c for row, c in zip(*h)]
    assert apply((M, v), x) == apply(f, apply(g, x))


if __name__ == '__main__':
    tests = [(n, t) for n, t in sorted(globals().items()) if n.startswith('test_')]
    for name, test in tests:
        test()
        print('ok  ', name)
    print(f'{len(tests)} tests passed')
