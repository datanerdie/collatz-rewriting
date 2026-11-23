#!/usr/bin/env python3
"""Dimension 2, natural numbers, no bound on the coefficients: a case analysis with z3.

Question, for the system T in one of the two search forms: is there a two-dimensional
natural matrix interpretation under which every rule is weakly decreasing and at least one
strict rule is strictly decreasing, in the sense of checker/check.py?

z3 cannot answer this as one question, so it is split (docs/dimension2.md has the proofs):

  1. End markers.  If an interpretation exists, one exists in which the matrix of the top end
     marker has a zero second row and a zero vector, and the other end marker has a zero
     matrix.  Only interpretations of that shape are searched.
  2. Zero patterns.  For each of the five digit matrices it is fixed which entries are zero.
     Patterns that contradict the carry rules are dropped, and of two patterns that differ by
     exchanging the two coordinates one is kept.
  3. Lemma I.  Equalities that follow from the carry rules are added, together with what
     follows from them by dividing out factors that the pattern makes positive (x*y = x*z
     with x > 0 gives y = z).  These do not change the answer; they make it reachable.
  4. Each pattern is first given to z3 as one integer problem.  If z3 does not decide it, the
     pattern is split further, by which entries of the top row are zero and which strict rule
     is strictly decreasing, and each part is tried over the integers and then over the real
     numbers (entries that the pattern makes positive are at least 1; the top row is scaled
     so that its smallest positive entry is 1; the strict rule decreases by at least 1).  An
     integer solution gives a real solution of this kind, so "no real solution" implies "no
     integer solution".
  5. Optionally (--t4), a part that is still undecided is split once more on a matrix entry
     x that the pattern makes positive: x = 1 or x >= 2.  Every such entry is tried until
     both halves of one split are refuted.

Verdict per pattern: "none" (every part refuted), "found" (z3 produced an integer solution
and checker/check.py accepted the certificate built from it), "undecided".

Usage:
  dimension2.py --selftest
  dimension2.py --form left|right [--jobs N] [--t1 S] [--t2 S] [--t3 S] [--t4 S] [--out DIR]
                [--again]       # re-run the patterns recorded as undecided
  dimension2.py --summary [--out DIR]
"""
import argparse
import itertools
import json
import multiprocessing
import os
import sys
import time

import sympy
import z3

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'checker'))

import systems                                                           # noqa: E402
from check import CertificateError, check, parse_problem, rule_str      # noqa: E402

DIGITS = 'abefg'            # f, t, 0, 1, 2 of the paper
BINARY, TERNARY = 'ab', 'efg'
BITS = [(0, 0), (0, 1), (1, 0), (1, 1)]     # bit k of a pattern is entry BITS[k]


# ---------------------------------------------------------------------------------------
# Zero patterns of 2x2 matrices, as 4-bit numbers
# ---------------------------------------------------------------------------------------

def bit(m, i, j):
    return (m >> (2 * i + j)) & 1


def pattern_product(x, y):
    """Pattern of a product of non-negative matrices with patterns x and y."""
    return sum(1 << (2 * i + j) for i, j in BITS
               if any(bit(x, i, k) and bit(y, k, j) for k in range(2)))


def pattern_swap(m):
    """Pattern after exchanging the two coordinates."""
    return sum(bit(m, i, j) << (2 * (1 - i) + (1 - j)) for i, j in BITS)


def digit_rules(rules):
    return [r for r in rules if all(s in DIGITS for s in r.left + r.right)]


def patterns(rules):
    """Zero patterns of the digit matrices that the digit-only rules allow, one per swap class.

    A weakly decreasing rule l -> r needs M_l >= M_r entrywise, so every entry that is
    positive in M_r is positive in M_l.
    """
    inner = digit_rules(rules)

    def of(string, p):
        m = p[DIGITS.index(string[0])]
        for s in string[1:]:
            m = pattern_product(m, p[DIGITS.index(s)])
        return m

    out = set()
    for p in itertools.product(range(16), repeat=5):
        if all(of(r.right, p) & ~of(r.left, p) == 0 for r in inner):
            out.add(min(p, tuple(pattern_swap(m) for m in p)))
    return sorted(out)


def pattern_class(p):
    up = any(bit(m, 0, 1) for m in p)
    lo = any(bit(m, 1, 0) for m in p)
    return 'irreducible' if up and lo else 'triangular' if up or lo else 'diagonal'


# ---------------------------------------------------------------------------------------
# Constraints
# ---------------------------------------------------------------------------------------

def is_carry_system(rules):
    """True if the digit-only rules are a one-to-one map between the six pairs (binary,
    ternary) and the six pairs (ternary, binary), in either orientation.  This is what the
    proof of Lemma I uses."""
    inner = digit_rules(rules)
    if len(inner) != 6 or any(len(r.left) != 2 or len(r.right) != 2 for r in inner):
        return False
    for first, second in ((BINARY, TERNARY), (TERNARY, BINARY)):
        lefts = {tuple(r.left) for r in inner}
        rights = {tuple(r.right) for r in inner}
        if (lefts == set(itertools.product(first, second))
                and rights == set(itertools.product(second, first))):
            return True
    return False


def cancel(equations, positive):
    """Consequences of polynomial equations in variables that are all positive.

    `equations` are sympy expressions that are zero; `positive` the set of their variables,
    each known to be positive.  If a polynomial that is zero factors, the factors that are
    positive (a monomial, or a polynomial with only positive coefficients) can be divided
    out.  When what remains is x - y for two variables, y is replaced by x everywhere, and the
    process is repeated.  Returns (pairs, reduced): pairs (x, y) of variables that are equal,
    and the polynomials that remain after dividing and replacing, each of which is zero.
    Every factorisation is checked by multiplying it out again.
    """
    def is_positive(f):
        poly = sympy.Poly(f, *sorted(f.free_symbols, key=str)) if f.free_symbols else None
        return (f.is_number and f > 0) or (poly is not None and all(c > 0 for c in poly.coeffs()))

    pairs, eqs = [], [sympy.expand(e) for e in equations]
    while True:
        reduced, merge = [], None
        for e in eqs:
            if e == 0:
                continue
            constant, factors = sympy.factor_list(e)
            assert sympy.expand(constant * sympy.Mul(*[f ** k for f, k in factors]) - e) == 0
            rest = [f for f, k in factors if not is_positive(f) and not is_positive(-f)]
            g = sympy.expand(sympy.Mul(*rest)) if rest else sympy.Integer(1)
            reduced.append(g)
            if merge is None and len(g.free_symbols) == 2 and g.free_symbols <= positive:
                x, y = sorted(g.free_symbols, key=str)
                if sympy.expand(g - (x - y)) == 0 or sympy.expand(g + (x - y)) == 0:
                    merge = (x, y)
        if merge is None:
            return pairs, [g for g in reduced if g != 0]
        pairs.append(merge)
        eqs = [sympy.expand(g.subs(merge[1], merge[0])) for g in reduced]


class Encoding:
    """The unknowns and constraints for one problem, one zero pattern and one number type."""

    def __init__(self, rules, pattern, real=False):
        self.rules, self.pattern, self.real = rules, pattern, real
        V = z3.Real if real else z3.Int
        self.top = next(r.left[0] for r in rules if r.strict)   # end marker at the top position
        ends = {s for r in rules for s in r.left + r.right} - set(DIGITS)
        assert self.top in ends and len(ends) <= 2, 'expected at most two end markers'
        self.other = (ends - {self.top} or {None}).pop()
        for r in rules:           # the top marker only in front, the other one only at the end
            for string in (r.left, r.right):
                assert self.top not in string[1:]
                assert self.other is None or self.other not in string[:-1]
                assert r.strict == (string[0] == self.top)

        self.M = {s: [[V(f'M{s}{i}{j}') for j in range(2)] for i in range(2)] for s in DIGITS}
        self.v = {s: [V(f'v{s}{i}') for i in range(2)] for s in DIGITS}
        self.row = [V('row0'), V('row1')]
        self.end = [V('end0'), V('end1')]
        zero = z3.RealVal(0) if real else z3.IntVal(0)
        self.M[self.top] = [self.row, [zero, zero]]
        self.v[self.top] = [zero, zero]
        if self.other:
            self.M[self.other] = [[zero, zero], [zero, zero]]
            self.v[self.other] = self.end

        cons = [x >= 0 for s in DIGITS for x in self.v[s]]
        cons += [x >= 0 for x in self.row + self.end]
        for s, m in zip(DIGITS, pattern):
            for i, j in BITS:
                cons.append(self.M[s][i][j] >= 1 if bit(m, i, j) else self.M[s][i][j] == 0)

        up = any(bit(m, 0, 1) for m in pattern)
        lo = any(bit(m, 1, 0) for m in pattern)
        lemma = is_carry_system(rules)
        self.names = {sympy.Symbol(f'M{s}{i}{j}', positive=True): self.M[s][i][j]
                      for s, m in zip(DIGITS, pattern) for i, j in BITS if bit(m, i, j)}
        equalities = []
        self.slack = {}
        for r in rules:
            if r.strict:
                # top u -> top w with [top] = (row; 0): the rule says row . (M_u - M_w) >= 0
                # and row . (v_u - v_w) >= 0, and it is strict if the latter is positive.
                (LM, Lv), (RM, Rv) = self.value(r.left[1:]), self.value(r.right[1:])
                normals = [[LM[i][j] - RM[i][j] for i in range(2)] for j in range(2)]
                normals.append([Lv[i] - Rv[i] for i in range(2)])
                cons += [self.dot(self.row, n) >= 0 for n in normals]
                self.slack[rule_str(r)] = self.dot(self.row, normals[-1])
                continue
            (LM, Lv), (RM, Rv) = self.value(r.left), self.value(r.right)
            cons += [LM[i][j] >= RM[i][j] for i, j in BITS] + [Lv[i] >= Rv[i] for i in range(2)]
            if lemma and all(s in DIGITS for s in r.left + r.right):
                # Lemma I, Corollary 2
                where = [(0, 0), (1, 1)] + ([(1, 0)] if up else []) + ([(0, 1)] if lo else [])
                cons += [LM[i][j] == RM[i][j] for i, j in where]
                SL, SR = self.symbolic(r.left), self.symbolic(r.right)
                equalities += [SL[i, j] - SR[i, j] for i, j in where]
        # Consequences of the equalities obtained by dividing out positive factors.
        pairs, reduced = cancel(equalities, set(self.names))
        term = lambda e: self.names[e] if e in self.names else int(e)
        for x, y in pairs:
            cons.append(self.names[x] == self.names[y])
        for g in reduced:
            total = 0
            for monomial, coefficient in g.as_coefficients_dict().items():
                product = int(coefficient)
                for base, power in monomial.as_powers_dict().items():
                    for _ in range(int(power)):
                        product = product * term(base)
                total = total + product
            cons.append(total == 0)
        self.constraints = cons

    def symbolic(self, string):
        """Matrix of a digit string with a symbol for each entry the pattern allows."""
        M = sympy.eye(2)
        for s in string:
            m = self.pattern[DIGITS.index(s)]
            M = M * sympy.Matrix(2, 2, lambda i, j: sympy.Symbol(f'M{s}{i}{j}', positive=True)
                                 if bit(m, i, j) else 0)
        return M

    @staticmethod
    def dot(x, y):
        return x[0] * y[0] + x[1] * y[1]

    def value(self, string):
        """(matrix, vector) of a string: the leftmost symbol is applied last."""
        one, zero = (z3.RealVal(1), z3.RealVal(0)) if self.real else (z3.IntVal(1), z3.IntVal(0))
        M, v = [[one, zero], [zero, one]], [zero, zero]
        for s in reversed(string):
            A, a = self.M[s], self.v[s]
            M, v = ([[sum(A[i][k] * M[k][j] for k in range(2)) for j in range(2)]
                     for i in range(2)],
                    [a[i] + sum(A[i][k] * v[k] for k in range(2)) for i in range(2)])
        return M, v

    def whole(self):
        """Some strict rule is strictly decreasing."""
        return self.constraints + [z3.Or([x > 0 for x in self.slack.values()])]

    def parts(self):
        """Names of the parts the question is split into: (zero pattern of the top row,
        strict rule)."""
        return [(rp, name) for rp in (1, 2, 3) for name in self.slack]

    def part(self, row_pattern, name):
        cons = list(self.constraints)
        for k in range(2):
            cons.append(self.row[k] >= 1 if (row_pattern >> k) & 1 else self.row[k] == 0)
        if self.real:
            if row_pattern == 3:
                cons.append(z3.Or(self.row[0] == 1, self.row[1] == 1))
            else:
                cons.append(self.row[0] + self.row[1] == 1)
        cons.append(self.slack[name] >= 1)
        return cons

    def certificate(self, model):
        get = lambda x: model.eval(x, model_completion=True).as_long()
        interp = {s: {'M': [[get(x) for x in row] for row in self.M[s]],
                      'v': [get(x) for x in self.v[s]]} for s in self.M}
        removed = [name for name, x in self.slack.items() if get(x) > 0]
        return {'type': 'natural', 'dimension': 2, 'removed': removed, 'interpretation': interp}


def solve(constraints, real, timeout):
    solver = z3.SolverFor('QF_NRA') if real else z3.Solver()
    solver.set('timeout', int(timeout * 1000))
    solver.add(constraints)
    answer = solver.check()
    return str(answer), (solver.model() if answer == z3.sat else None)


def decide(problem_text, pattern, t1, t2, t3, t4=0):
    """Verdict for one zero pattern: ('none' | 'found' | 'undecided', detail)."""
    rules, is_top = parse_problem(problem_text)
    assert is_top
    enc = Encoding(rules, pattern)

    def found(model):
        cert = enc.certificate(model)
        try:
            check(problem_text, {'steps': [cert]}, allow_partial=True)
        except CertificateError as e:
            return 'undecided', {'error': f'z3 model rejected by the checker: {e}'}
        return 'found', {'certificate': cert}

    answer, model = solve(enc.whole(), False, t1)
    if answer == 'unsat':
        return 'none', {'how': 'whole'}
    if answer == 'sat':
        return found(model)
    real = Encoding(rules, pattern, real=True)

    def both(rp, name, extra, limit_int, limit_real):
        """One part with extra conditions on matrix entries: integers, then real numbers."""
        answer, model = solve(enc.part(rp, name) + [f(enc) for f in extra], False, limit_int)
        if answer != 'unknown':
            return answer, model, 'int'
        answer, _ = solve(real.part(rp, name) + [f(real) for f in extra], True, limit_real)
        # a real solution says nothing about the integers
        return ('unsat' if answer == 'unsat' else 'undecided'), None, 'real'

    parts = []
    for rp, name in enc.parts():
        answer, model, how = both(rp, name, [], t2, t3)
        if answer == 'sat':
            return found(model)
        if answer != 'unsat' and t4:
            # Split on one positive matrix entry x: either x = 1 or x >= 2.
            for s, m in zip(DIGITS, pattern):
                for i, j in BITS:
                    if not bit(m, i, j) or answer == 'unsat':
                        continue
                    halves = [both(rp, name, [extra], t4, t4) for extra in
                              (lambda e: e.M[s][i][j] == 1, lambda e: e.M[s][i][j] >= 2)]
                    for half in halves:
                        if half[0] == 'sat':
                            return found(half[1])
                    if all(half[0] == 'unsat' for half in halves):
                        answer, how = 'unsat', f'split on M{s}{i}{j}'
        parts.append([rp, name, answer, how])
    verdict = 'none' if all(x[2] == 'unsat' for x in parts) else 'undecided'
    return verdict, {'how': 'parts', 'parts': parts}


# ---------------------------------------------------------------------------------------
# Self-test: the encoding must not refute things that are true
# ---------------------------------------------------------------------------------------

def without(problem_text, dropped):
    return ''.join(line + '\n' for line in problem_text.splitlines()
                   if line.split()[0] + ' ' + line.split()[2] not in dropped)


def selftest():
    ok = True

    def report(name, good, note=''):
        nonlocal ok
        ok = ok and good
        print(('ok    ' if good else 'FAIL  ') + name + (': ' + note if note else ''))

    # 1. The representation of the value of a string satisfies every weak constraint of T,
    #    in both forms.  Matrices of products do not commute here, so this checks the order
    #    in which every rule is encoded.
    value = {'a': [[2, 0], [0, 1]], 'b': [[2, 0], [1, 1]], 'e': [[3, 0], [0, 1]],
             'f': [[3, 0], [1, 1]], 'g': [[3, 0], [2, 1]]}
    for form in ('left', 'right'):
        text = systems.COLLATZ.search_problem(form)
        rules, _ = parse_problem(text)
        mats = value if form == 'left' else {s: [list(c) for c in zip(*m)]
                                             for s, m in value.items()}
        p = tuple(sum(1 << k for k, (i, j) in enumerate(BITS) if mats[s][i][j]) for s in DIGITS)
        enc = Encoding(rules, p)
        fix = [enc.M[s][i][j] == mats[s][i][j] for s in DIGITS for i, j in BITS]
        fix += [x == 0 for s in DIGITS for x in enc.v[s]]
        row = [1, 1] if form == 'left' else [0, 1]
        fix += [enc.row[k] == row[k] for k in range(2)]
        answer, _ = solve(enc.constraints + fix, False, 60)
        report(f'value representation satisfies the weak constraints ({form} form)',
               answer == 'sat', answer)
        canon = min(p, tuple(pattern_swap(m) for m in p))
        report(f'its zero pattern is among the cases ({form} form)', canon in patterns(rules))
        other = {s: [list(c) for c in zip(*m)] for s, m in mats.items()}
        fix = [enc.M[s][i][j] == other[s][i][j] for s in DIGITS for i, j in BITS]
        answer, _ = solve([c for c in Encoding(rules, tuple(
            sum(1 << k for k, (i, j) in enumerate(BITS) if other[s][i][j]) for s in DIGITS)
        ).constraints] + fix, False, 60)
        report(f'the transposed representation violates them ({form} form)',
               answer == 'unsat', answer)

    # 2. Systems that do have an interpretation: the search finds one and the checker
    #    accepts it.  Left form without the rule for odd numbers; right form without the
    #    left-end rules.
    controls = [('left', {'bd gd'}, 'T without t▷ → 2▷'),
                ('right', {'ec bc', 'fc aac', 'gc bac'}, 'T without the left-end rules')]
    for form, dropped, title in controls:
        text = without(systems.COLLATZ.search_problem(form), dropped)
        rules, _ = parse_problem(text)
        assert len(rules) == 11 - len(dropped)
        hit = None
        for p in [(9, 9, 9, 9, 9)] + patterns(rules)[:200]:
            verdict, detail = decide(text, p, 10, 5, 5)
            if verdict == 'found':
                hit = (p, detail['certificate']['removed'])
                break
        report(f'control with a known proof, {form} form ({title})', hit is not None,
               f'pattern {hit[0]}, removes {hit[1]}' if hit else 'nothing found')
    return ok


# ---------------------------------------------------------------------------------------

def work(job):
    form, p, t1, t2, t3, t4 = job
    start = time.time()
    verdict, detail = decide(systems.COLLATZ.search_problem(form), tuple(p), t1, t2, t3, t4)
    return {'form': form, 'pattern': list(p), 'class': pattern_class(p), 'verdict': verdict,
            'seconds': round(time.time() - start, 1), 'detail': detail}


def load(path):
    done = {}
    if os.path.exists(path):
        with open(path) as f:
            for line in f:
                r = json.loads(line)
                done[tuple(r['pattern'])] = r          # a later record replaces an earlier one
    return done


def run(args):
    os.makedirs(args.out, exist_ok=True)
    path = os.path.join(args.out, f'{args.form}.jsonl')
    rules, _ = parse_problem(systems.COLLATZ.search_problem(args.form))
    todo = patterns(rules)
    done = load(path)
    if args.again:
        todo = [p for p in todo if p in done and done[p]['verdict'] == 'undecided']
    else:
        todo = [p for p in todo if p not in done]
    print(f'{args.form} form: {len(done)} patterns recorded, {len(todo)} to do', flush=True)
    jobs = [(args.form, p, args.t1, args.t2, args.t3, args.t4) for p in todo]
    with multiprocessing.Pool(args.jobs) as pool, open(path, 'a') as f:
        for r in pool.imap_unordered(work, jobs):
            f.write(json.dumps(r) + '\n')
            f.flush()
            if r['verdict'] != 'none':
                print(r['pattern'], r['verdict'], r['seconds'], flush=True)
    done = load(path)
    with open(path, 'w') as f:
        for p in sorted(done):
            f.write(json.dumps(done[p]) + '\n')
    print('done', flush=True)


def summary(args):
    out = ['# Dimension 2 with unbounded coefficients: case analysis for the system T',
           '',
           'Produced by `harness/dimension2.py` with z3 ' + z3.get_version_string() + '.',
           'The method and the proofs it relies on are in `docs/dimension2.md`.',
           '',
           'For each zero pattern of the five digit matrices: is there a two-dimensional natural',
           'interpretation with that pattern under which every rule of T is weakly decreasing',
           'and some strict rule is strictly decreasing?',
           '',
           '- "none": z3 refuted every part of the case.',
           '- "found": z3 produced an interpretation and `checker/check.py` accepted it.',
           '- "undecided": z3 gave no answer within the time limits for at least one part.',
           '',
           '| Form | Patterns | None | Found | Undecided |', '|---|---|---|---|---|']
    details = []
    for form in ('left', 'right'):
        path = os.path.join(args.out, f'{form}.jsonl')
        if not os.path.exists(path):
            continue
        rs = list(load(path).values())
        count = lambda v, c=None: sum(1 for r in rs if r['verdict'] == v
                                      and (c is None or r['class'] == c))
        out.append(f'| {form} | {len(rs):,} | {count("none"):,} | {count("found")} | '
                   f'{count("undecided")} |')
        details += ['', f'## {form.capitalize()} form', '',
                    '| Kind of pattern | Patterns | None | Found | Undecided |',
                    '|---|---|---|---|---|']
        for c in ('irreducible', 'triangular', 'diagonal'):
            n = sum(1 for r in rs if r['class'] == c)
            details.append(f'| {c} | {n:,} | {count("none", c):,} | {count("found", c)} | '
                           f'{count("undecided", c)} |')
        whole = sum(1 for r in rs if r['verdict'] == 'none' and r['detail']['how'] == 'whole')
        split = [r for r in rs if r['verdict'] == 'none' and r['detail']['how'] == 'parts']
        with_real = sum(1 for r in split if any(x[3] == 'real' for x in r['detail']['parts']))
        with_split = sum(1 for r in split
                         if any(x[3].startswith('split') for x in r['detail']['parts']))
        details += ['',
                    f'Refuted as one integer problem: {whole:,}. Refuted after splitting: '
                    f'{len(split)}, of which {with_real} needed the real-number procedure for '
                    f'at least one part and {with_split} a further split on a matrix entry.']
        open_ = [r for r in rs if r['verdict'] == 'undecided']
        if open_:
            details += ['', 'Undecided patterns (entries of each digit matrix that may be '
                        'non-zero, as a 4-bit number: 1 top left, 2 top right, 4 bottom left, '
                        '8 bottom right; order f, t, 0, 1, 2):', '']
            details += [f'- `{r["pattern"]}` ({r["class"]})' for r in open_]
        for r in rs:
            if r['verdict'] == 'found':
                details += ['', f'Found for pattern `{r["pattern"]}`: '
                            + json.dumps(r['detail']['certificate'])]
    out += details
    with open(os.path.join(args.out, 'summary.md'), 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('\n'.join(out[13:]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--selftest', action='store_true')
    ap.add_argument('--summary', action='store_true')
    ap.add_argument('--form', choices=('left', 'right'))
    ap.add_argument('--jobs', type=int, default=os.cpu_count() or 1)
    ap.add_argument('--t1', type=float, default=10, help='seconds, whole pattern, integers')
    ap.add_argument('--t2', type=float, default=30, help='seconds per part, integers')
    ap.add_argument('--t3', type=float, default=30, help='seconds per part, real numbers')
    ap.add_argument('--t4', type=float, default=0,
                    help='seconds per half when an undecided part is split on a matrix entry '
                         '(0: no splitting)')
    ap.add_argument('--again', action='store_true',
                    help='re-run the patterns recorded as undecided (with other time limits)')
    ap.add_argument('--out', default=os.path.join(ROOT, 'results', 'dimension2'))
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    if args.form:
        run(args)
    if args.summary:
        summary(args)


if __name__ == '__main__':
    main()
