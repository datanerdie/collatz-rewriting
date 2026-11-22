#!/usr/bin/env python3
"""Run the published Yolcu-Aaronson-Heule prover on one problem and save a certificate.

The published prover prints its interpretations as ASCII art.  This wrapper runs it
unmodified, in-process, and additionally records every interpretation it finds as JSON so
that `checker/check.py` can verify the result without trusting the prover.

Two small accommodations are made, neither of which touches the search:

  * the prover calls `random.randint(0, 1e9)`, which newer Python versions reject because
    1e9 is a float; the bound is converted to an integer;
  * the prover shells out to `./cadical`; the working directory is given a `cadical` that is
    `harness/cadical`, a stand-in backed by the python-sat package.

Usage:  run_published.py PROBLEM.srs CERTIFICATE.json [prover options...]
"""
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
PROVER = os.path.join(ROOT, 'third_party', 'rewriting-collatz', 'prover')


def true_value(kind, raw, negwidth):
    """Undo the prover's internal coding of coefficients."""
    raw = int(raw)
    if kind == 'natural':
        return raw
    return None if raw == 0 else raw - 1 - negwidth      # arctic: 0 codes -infinity


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    problem = os.path.abspath(sys.argv[1])
    out = os.path.abspath(sys.argv[2])
    options = sys.argv[3:]
    if not os.path.isdir(PROVER):
        sys.exit('published prover not found; run scripts/fetch_baseline.sh first')

    work = os.path.join(ROOT, 'work')
    os.makedirs(work, exist_ok=True)
    shim = os.path.join(work, 'cadical')
    if not os.path.exists(shim):
        os.symlink(os.path.join(HERE, 'cadical'), shim)
    os.chdir(work)
    # The stand-in solver is started through `env python3`; make that this interpreter.
    os.environ['PATH'] = os.path.dirname(sys.executable) + os.pathsep + os.environ['PATH']

    sys.path.append(PROVER)                 # appended, so it cannot shadow the standard library
    _randint = random.randint
    random.randint = lambda a, b: _randint(int(a), int(b))

    import decoder
    import main as prover

    steps = []
    original_check = decoder.Decoder.check

    def recording_check(self, system, interp):
        kind = type(self).__name__.replace('Decoder', '').lower()
        negwidth = getattr(self, 'negwidth', 0)
        d = self.dimension
        table = {}
        for sym in sorted(system.symbols):
            M, v = interp[sym]
            table[sym[0]] = {
                'M': [[true_value(kind, M[i][j], negwidth) for j in range(d)] for i in range(d)],
                'v': [None if v is None else true_value(kind, v[i], negwidth) for i in range(d)],
            }
        removable = original_check(self, system, interp)
        steps.append({'type': kind, 'dimension': d, 'interpretation': table,
                      'removed': [str(r) for r in removable]})
        return removable

    decoder.Decoder.check = recording_check

    sys.argv = ['main.py', problem] + options
    start = time.time()
    try:
        prover.main()
        code = 0
    except SystemExit as e:
        code = e.code
    elapsed = time.time() - start

    with open(problem) as f:
        rules = [line.strip() for line in f if line.strip()]
    status = {19: 'QED', 11: 'strict rules remain', 29: 'UNSAT'}.get(code, f'exit {code}')
    with open(out, 'w') as f:
        json.dump({'problem': os.path.basename(problem), 'rules': rules, 'steps': steps,
                   'prover': {'options': options, 'status': status,
                              'seconds': round(elapsed, 3),
                              'solver': os.environ.get('PYSAT_SOLVER', 'cadical195')}},
                  f, indent=1)
        f.write('\n')
    print(f'\n[{status}] {len(steps)} step(s), {elapsed:.2f} s -> {out}', file=sys.stderr)
    sys.exit(0 if code == 19 else 1)


if __name__ == '__main__':
    main()
