#!/usr/bin/env python3
"""Dimension 1, with no bound on the coefficients: does any interpretation exist?

Phase 3 asked a SAT solver whether an interpretation exists with coefficients below a fixed
bound.  This script asks an SMT solver (z3) the same question for dimension 1 with unbounded
integer coefficients.  For each problem it decides whether there is a one-dimensional
interpretation, natural or arctic, under which every rule is weakly decreasing and at least
one strict rule is strictly decreasing, in the sense of checker/check.py.

  natural   [s](x) = p*x + q with p, q >= 0.  The constraints contain products of unknowns
            (non-linear integer arithmetic), which z3 may fail to decide; "unknown" is then
            reported.  For the system T a written proof is in docs/dimension1.md.
  arctic    [s](x) = max(m + x, v) with m, v integers or minus infinity, entries below zero
            allowed.  The constraints are linear, so z3 decides them.

In dimension 1 the comparison used by the checker is exact for natural interpretations:
p*x + q >= p'*x + q' holds for every x >= 0 exactly when p >= p' and q >= q'.  So "none" for
natural means that no weakly monotone affine function on the natural numbers works at all.

A "none" verdict rests on z3.  A "found" verdict is turned into a certificate and verified by
checker/check.py.

Usage:  dimension1.py [--timeout SECONDS] [--jobs N] [--out results/dimension1]
"""
import argparse
import json
import multiprocessing
import os
import sys

import z3

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'checker'))

import phase3                                                            # noqa: E402
from check import CertificateError, check, parse_problem, rule_str      # noqa: E402


# ---------------------------------------------------------------------------------------
# Natural numbers: [s](x) = p*x + q
# ---------------------------------------------------------------------------------------

def natural(rules, symbols):
    p = {s: z3.Int(f'p_{s}') for s in symbols}
    q = {s: z3.Int(f'q_{s}') for s in symbols}
    constraints = [v >= 0 for v in list(p.values()) + list(q.values())]

    def value(string):
        P, Q = p[string[0]], q[string[0]]
        for s in string[1:]:
            P, Q = P * p[s], P * q[s] + Q          # outer after inner
        return P, Q

    strict = []
    for r in rules:
        (PL, QL), (PR, QR) = value(r.left), value(r.right)
        constraints += [PL >= PR, QL >= QR]
        if r.strict:
            strict.append((r, QL > QR))

    def certificate(model, removed):
        get = lambda v: model.eval(v, model_completion=True).as_long()
        return {'type': 'natural', 'dimension': 1, 'removed': removed,
                'interpretation': {s: {'M': [[get(p[s])]], 'v': [get(q[s])]} for s in symbols}}

    return constraints, strict, certificate


# ---------------------------------------------------------------------------------------
# Arctic numbers: [s](x) = max(m + x, v); a number is (finite?, value)
# ---------------------------------------------------------------------------------------

def a_mul(x, y):
    return z3.And(x[0], y[0]), x[1] + y[1]


def a_add(x, y):
    both = z3.And(x[0], y[0])
    return z3.Or(x[0], y[0]), z3.If(both, z3.If(x[1] >= y[1], x[1], y[1]),
                                    z3.If(x[0], x[1], y[1]))


def a_ge(x, y):
    return z3.Or(z3.Not(y[0]), z3.And(x[0], x[1] >= y[1]))


def a_gg(x, y):
    return z3.If(x[0], z3.Or(z3.Not(y[0]), x[1] > y[1]), z3.Not(y[0]))


def arctic(rules, symbols):
    m = {s: (z3.Bool(f'mf_{s}'), z3.Int(f'm_{s}')) for s in symbols}
    v = {s: (z3.Bool(f'vf_{s}'), z3.Int(f'v_{s}')) for s in symbols}
    nonneg = lambda x: z3.And(x[0], x[1] >= 0)
    # The condition of a weakly monotone algebra: [s] maps the carrier into itself.
    constraints = [z3.Or(nonneg(m[s]), nonneg(v[s])) for s in symbols]

    def value(string):
        M, V = m[string[0]], v[string[0]]
        for s in string[1:]:
            M, V = a_mul(M, m[s]), a_add(a_mul(M, v[s]), V)
        return M, V

    strict = []
    for r in rules:
        (ML, VL), (MR, VR) = value(r.left), value(r.right)
        constraints += [a_ge(ML, MR), a_ge(VL, VR)]
        if r.strict:
            strict.append((r, z3.And(a_gg(ML, MR), a_gg(VL, VR))))

    def certificate(model, removed):
        def get(x):
            if not z3.is_true(model.eval(x[0], model_completion=True)):
                return None
            return model.eval(x[1], model_completion=True).as_long()
        return {'type': 'arctic', 'dimension': 1, 'removed': removed,
                'interpretation': {s: {'M': [[get(m[s])]], 'v': [get(v[s])]} for s in symbols}}

    return constraints, strict, certificate


# ---------------------------------------------------------------------------------------

def decide(problem_text, kind, timeout):
    """('none' | 'found' | 'unknown', detail) for one problem and one interpretation type."""
    rules, is_top = parse_problem(problem_text)
    if not is_top:
        raise SystemExit('only top termination problems are handled')
    symbols = sorted({s for r in rules for s in r.left + r.right})
    constraints, strict, certificate = (natural if kind == 'natural' else arctic)(rules, symbols)
    solver = z3.Solver()
    solver.set('timeout', timeout * 1000)
    solver.add(constraints)
    solver.add(z3.Or([cond for _, cond in strict]))
    answer = solver.check()
    if answer == z3.unsat:
        return 'none', None
    if answer != z3.sat:
        return 'unknown', solver.reason_unknown()
    model = solver.model()
    removed = [rule_str(r) for r, cond in strict if z3.is_true(model.eval(cond))]
    step = certificate(model, removed)
    try:
        check(problem_text, {'steps': [step]}, allow_partial=True)
    except CertificateError as e:
        return 'unknown', f'z3 model rejected by the checker: {e}'
    return 'found', step


def work(job):
    i, kind, timeout = job
    problem = phase3.all_problems()[i]
    answer = decide(problem['system'].search_problem(problem['side']), kind, timeout)
    print(f'{problem["group"]:9s} {problem["name"]:34s} {kind:8s} {answer[0]}', flush=True)
    return (i, kind), answer


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--timeout', type=int, default=120)
    ap.add_argument('--jobs', type=int, default=os.cpu_count() or 1)
    ap.add_argument('--out', default=os.path.join(ROOT, 'results', 'dimension1'))
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)

    problems = phase3.all_problems()
    jobs = [(i, kind, args.timeout) for i in range(len(problems))
            for kind in ('natural', 'arctic')]
    with multiprocessing.Pool(args.jobs) as pool:
        answers = dict(pool.imap_unordered(work, jobs))

    rows, records = [], []
    for i, problem in enumerate(problems):
        cells = []
        for kind in ('natural', 'arctic'):
            verdict, detail = answers[i, kind]
            records.append({'problem': problem['name'], 'group': problem['group'],
                            'type': kind, 'verdict': verdict,
                            'detail': detail if verdict != 'none' else None})
            cells.append(verdict if verdict != 'found'
                         else 'found, removes ' + ', '.join(f'`{r}`' for r in detail['removed']))
        rows.append((problem, cells))

    with open(os.path.join(args.out, 'verdicts.jsonl'), 'w') as f:
        for r in records:
            f.write(json.dumps(r) + '\n')

    out = ['# Dimension 1 with unbounded coefficients',
           '',
           'Produced by `harness/dimension1.py` with z3 ' + z3.get_version_string() + '.',
           'For each problem: is there a one-dimensional interpretation, with integer',
           'coefficients of any size, that makes every rule weakly decreasing and at least one',
           'strict rule strictly decreasing?',
           '',
           '- "none": z3 reports that no such interpretation exists. For natural interpretations',
           '  this is a statement about every weakly monotone affine function on the natural',
           '  numbers. It rests on z3; for the system T there is also a written proof in',
           '  `docs/dimension1.md`.',
           '- "found": z3 produced one and `checker/check.py` accepted it; the rules it removes',
           '  are listed (as written in the problem file, reversed in the right form).',
           '- "unknown": z3 did not decide within ' + str(args.timeout) + ' seconds.',
           '- Arctic interpretations here may have entries below zero, which Phase 3 did not',
           '  search.']
    titles = {'full': 'The Collatz conjecture itself',
              'negative': 'Negative controls: systems that loop',
              'target': 'Targets: statements the paper leaves open',
              'control': 'Controls: statements the paper proved'}
    for group in ('full', 'negative', 'target', 'control'):
        out += ['', f'## {titles[group]}', '', '| Problem | Rules | Natural | Arctic |',
                '|---|---|---|---|']
        for problem, cells in rows:
            if problem['group'] == group:
                out.append(f'| {problem["name"]} | {len(problem["system"].rules)} | '
                           f'{cells[0]} | {cells[1]} |')
    counts = {}
    for r in records:
        key = (r['group'], r['type'], r['verdict'])
        counts[key] = counts.get(key, 0) + 1
    out += ['', '## Totals', '', '| Group | Type | None | Found | Unknown |', '|---|---|---|---|---|']
    for group in ('full', 'negative', 'target', 'control'):
        for kind in ('natural', 'arctic'):
            out.append(f'| {group} | {kind} | ' + ' | '.join(
                str(counts.get((group, kind, v), 0)) for v in ('none', 'found', 'unknown')) + ' |')
    with open(os.path.join(args.out, 'summary.md'), 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('\n'.join(out[-9:]))


if __name__ == '__main__':
    main()
