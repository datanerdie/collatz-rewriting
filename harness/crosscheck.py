#!/usr/bin/env python3
"""Re-run a sample of the Phase 3 "ruled out" verdicts with a different SAT solver.

A "ruled out" run is one where the solver reported that no interpretation of the given type,
dimension and coefficient range removes any strict rule.  Such a verdict cannot be checked by
checker/check.py, because there is no certificate.  This script repeats a deterministic sample
of those runs with another solver from the python-sat package and compares the verdicts.  The
prover is run with the same options, so both solvers see the same formula.

Agreement is evidence against a solver bug.  It is not evidence against a bug in the encoding,
which both solvers share; the control group, where proofs are found and verified, is the check
on that.

Usage:  crosscheck.py [--solver glucose4] [--every 10] [--timeout 120] [--jobs 4]
"""
import argparse
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import phase3                                                            # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--solver', default='glucose4')
    ap.add_argument('--every', type=int, default=10)
    ap.add_argument('--timeout', type=int, default=120)
    ap.add_argument('--jobs', type=int, default=os.cpu_count() or 1)
    args = ap.parse_args()

    with open(os.path.join(phase3.RESULTS, 'runs.jsonl')) as f:
        runs = [json.loads(line) for line in f if line.strip()]
    pool = sorted((r for r in runs if r['status'] == 'UNSAT' and r['removed'] == 0),
                  key=lambda r: (r['problem'], r['type'], r['dimension'], r['values']))
    sample = pool[::args.every]

    os.environ['PYSAT_SOLVER'] = args.solver
    phase3.CERTS = os.path.join(phase3.LIVE, 'crosscheck-' + args.solver)
    os.makedirs(phase3.CERTS, exist_ok=True)
    problems = {p['name']: p for p in phase3.all_problems()}

    def again(r):
        new = phase3.run_one(problems[r['problem']], (r['type'], r['dimension'], r['values']),
                             args.timeout)
        print(f'{r["problem"]:34s} {r["type"]:8s} d={r["dimension"]} w={r["values"]:<3d} '
              f'{new["status"]:10s} {new["seconds"]:6.1f} s', flush=True)
        return r, new

    with ThreadPoolExecutor(args.jobs) as executor:
        results = list(executor.map(again, sample))

    agree = [x for x in results if x[1]['status'] == 'UNSAT']
    undecided = [x for x in results if x[1]['status'] == 'timeout']
    differ = [x for x in results if x[1]['status'] not in ('UNSAT', 'timeout')]
    groups = {}
    for r, _ in results:
        groups[r['group']] = groups.get(r['group'], 0) + 1
    dims = {}
    for r, _ in agree:
        dims[r['dimension']] = dims.get(r['dimension'], 0) + 1

    out = ['# Phase 3: cross-check of "ruled out" verdicts',
           '',
           'Produced by `harness/crosscheck.py`. The search used the solver `cadical195` from the',
           f'python-sat package. Every {args.every}th run that ended with "no interpretation of',
           'this size removes any strict rule" (sorted by problem and configuration) was repeated',
           f'with the solver `{args.solver}` under a {args.timeout} second limit.',
           '',
           f'- Verdicts available for the sample: {len(pool):,}; sampled: {len(sample)}.',
           '- Sample by group: ' + ', '.join(f'{g} {n}' for g, n in sorted(groups.items())) + '.',
           f'- Second solver agrees (also reports none exists): {len(agree)}'
           + (' (by dimension: ' + ', '.join(f'{d}: {n}' for d, n in sorted(dims.items())) + ')'
              if agree else '') + '.',
           f'- Second solver undecided within the limit: {len(undecided)}.',
           f'- Second solver disagrees: {len(differ)}.']
    for r, new in differ:
        out.append(f'  - {r["problem"]} {r["type"]} d={r["dimension"]} w={r["values"]}: '
                   f'{new["status"]}, checker: {new["checker"]}')
    out += ['',
            'Agreement is evidence against a solver bug, not against a bug in the encoding that',
            'both solvers are given. A "ruled out" verdict is still not a certified result.']
    with open(os.path.join(phase3.RESULTS, 'crosscheck.md'), 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('\n'.join(out))
    return 1 if differ else 0


if __name__ == '__main__':
    sys.exit(main())
