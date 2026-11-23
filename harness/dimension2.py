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
  5. Optionally (--t4), a part that is still undecided is split once more: each diagonal
     entry that the pattern makes positive is either 1 or at least 2 (entries that Lemma I
     shows to be equal are treated as one).  A combination that is still undecided is split
     again on one entry off the diagonal, x = 1 or x >= 2, each such entry being tried
     until both halves of one split are refuted.

Verdict per pattern: "none" (every part refuted), "found" (z3 produced an integer solution
and checker/check.py accepted the certificate built from it), "undecided".

A second pass (--hand) takes the patterns that the first pass left undecided and uses
results that are proved in writing in docs/dimension2.md:

  Theorem 6   (both forms) no two-dimensional interpretation exists in which the matrix of t
              or the matrix of 2 has both entries off the diagonal positive and the matrix of
              f has both diagonal entries positive.  Such a pattern needs no solver.
  Theorem 8   (both forms) no two-dimensional interpretation exists in which the matrix of
              f has both entries off the diagonal positive, nor one in which the digit
              matrices are irreducible and the pattern makes those of f, t and 0
              invertible.  Such a pattern needs no solver.
  Lemma III   (left form) an interpretation in which the vector of the digit 2 is zero makes
              no rule strict; so for the other patterns that vector is required to be
              non-zero, and z3 is run again.
  Corollary 10 (both forms) if the digit matrices are irreducible and those of f, t, 0 are
              invertible, then t = f and 0 = 1 = 2 as matrices, or the traces and
              determinants are those of the value representation; added as a condition.
  Lemma IV    (both forms) if every digit matrix is upper triangular, the first entry of the
              top row is positive and some vector has a non-zero second entry, because
              otherwise one coordinate would be a one-dimensional interpretation, which
              Theorem 4 excludes.  The same with the coordinates exchanged.

The first pass is recorded in {form}.jsonl and rests on z3 alone; the second pass is recorded
in {form}-hand.jsonl.

Usage:
  dimension2.py --selftest
  dimension2.py --form left|right [--jobs N] [--t1 S] [--t2 S] [--t3 S] [--t4 S] [--out DIR]
                [--again]       # re-run the patterns recorded as undecided
                [--hand]        # second pass, for the patterns undecided in the first
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


# ---------------------------------------------------------------------------------------
# Results with a written proof (docs/dimension2.md, section 3)
# ---------------------------------------------------------------------------------------

def lemma3_applies(rules):
    """Lemma III uses these five rules of the left form and no others."""
    have = {(''.join(r.left), ''.join(r.right), bool(r.strict)) for r in rules}
    return {('ag', 'fa', False), ('af', 'eb', False), ('ce', 'cb', True), ('cf', 'caa', True),
            ('cg', 'cab', True)} <= have


def is_full_system(rules):
    """The rules are those of T, in one of its two search forms."""
    have = {(''.join(r.left), ''.join(r.right), bool(r.strict)) for r in rules}
    for form in ('left', 'right'):
        full, _ = parse_problem(systems.COLLATZ.search_problem(form))
        if have == {(''.join(r.left), ''.join(r.right), bool(r.strict)) for r in full}:
            return True
    return False


def theorem6(pattern):
    """True if Theorem 6 excludes every interpretation of the full system T, in either form,
    with this zero pattern: the matrix of t or of 2 is irreducible and the diagonal of the
    matrix of f is positive."""
    A, B, G = pattern[0], pattern[1], pattern[4]
    irreducible = lambda m: bit(m, 0, 1) and bit(m, 1, 0)
    return bool(bit(A, 0, 0) and bit(A, 1, 1) and (irreducible(B) or irreducible(G)))


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

    def __init__(self, rules, pattern, real=False, hand=False):
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
        self.equal = [(str(x), str(y)) for x, y in pairs]     # entries known to be equal
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
        if hand and lemma3_applies(rules):
            cons.append(z3.Or([x > 0 for x in self.v['g']]))
        if hand and is_full_system(rules):
            # Lemma IV.  k is the coordinate that the digit matrices do not feed into the
            # other one: 1 if they are all upper triangular, 0 if all lower triangular.
            for k, triangular in ((1, not lo), (0, not up)):
                if triangular:
                    cons.append(self.row[1 - k] > 0)
                    cons.append(z3.Or([self.v[s][k] > 0 for s in DIGITS] + [self.end[k] > 0]))
        if hand and is_full_system(rules) and up and lo:
            cons.append(self.corollary10())
        self.constraints = cons

    def trace(self, s):
        return self.M[s][0][0] + self.M[s][1][1]

    def det(self, s):
        return self.M[s][0][0] * self.M[s][1][1] - self.M[s][0][1] * self.M[s][1][0]

    def value_like(self):
        """The traces and determinants of the digit matrices are those of the value
        representation: f, t have eigenvalues m, 2m and 0, 1, 2 have eigenvalues n, 3n."""
        tr, det = self.trace, self.det
        return [2 * tr('a') * tr('a') == 9 * det('a'), tr('b') == tr('a'), det('b') == det('a'),
                3 * tr('e') * tr('e') == 16 * det('e'), tr('f') == tr('e'), tr('g') == tr('e'),
                det('f') == det('e'), det('g') == det('e')]

    def corollary10(self):
        """Digit matrices irreducible, both forms: the condition of Corollary 10 of
        docs/dimension2.md."""
        same = lambda s, t: z3.And([self.M[s][i][j] == self.M[t][i][j] for i, j in BITS])
        return z3.Implies(z3.And(self.det('a') != 0, self.det('b') != 0, self.det('e') != 0),
                          z3.Or(z3.And(same('a', 'b'), same('e', 'f'), same('f', 'g')),
                                z3.And(self.value_like())))

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

    def diagonal(self):
        """The diagonal entries that the pattern makes positive, one from each group of
        entries that are known to be equal: a list of (symbol, i)."""
        leader = {}

        def find(x):
            while leader.get(x, x) != x:
                x = leader[x]
            return x

        for x, y in self.equal:
            leader[find(y)] = find(x)
        seen, out = set(), []
        for s, m in zip(DIGITS, self.pattern):
            for i in range(2):
                if bit(m, i, i) and find(f'M{s}{i}{i}') not in seen:
                    seen.add(find(f'M{s}{i}{i}'))
                    out.append((s, i))
        return out

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


def surely_invertible(m):
    """True if every matrix with this zero pattern has a non-zero determinant: exactly one of
    the two products 'diagonal' and 'off the diagonal' is positive."""
    return bool(bit(m, 0, 0) and bit(m, 1, 1)) != bool(bit(m, 0, 1) and bit(m, 1, 0))


def theorem8(pattern, form=None):
    """True if Theorem 8 excludes every interpretation of the full system T, in either form,
    with this zero pattern: the matrix of f is irreducible, or the digit matrices are
    irreducible and the pattern makes those of f, t and 0 invertible."""
    A = pattern[0]
    return bool(bit(A, 0, 1) and bit(A, 1, 0)) or (
        pattern_class(pattern) == 'irreducible'
        and all(surely_invertible(m) for m in pattern[:3]))


def by_theorem(pattern, form):
    """The written theorem that excludes the pattern, or None."""
    if theorem6(pattern):
        return 'theorem 6'
    if theorem8(pattern, form):
        return 'theorem 8'
    return None


def form_of(rules):
    """'left' or 'right' if the rules are those of the full system T in that form."""
    key = lambda rs: sorted((''.join(r.left), ''.join(r.right), bool(r.strict)) for r in rs)
    for form in ('left', 'right'):
        if key(rules) == key(parse_problem(systems.COLLATZ.search_problem(form))[0]):
            return form
    return None


def decide(problem_text, pattern, t1, t2, t3, t4=0, hand=False):
    """Verdict for one zero pattern: ('none' | 'found' | 'undecided', detail).

    With hand=True the problem must be the full system T in one of its two forms, and the
    written results of docs/dimension2.md are used as described at the top of this file.
    """
    rules, is_top = parse_problem(problem_text)
    assert is_top
    if hand and by_theorem(pattern, form_of(rules)):
        return 'none', {'how': by_theorem(pattern, form_of(rules))}
    enc = Encoding(rules, pattern, hand=hand)
    reals = []

    def real():
        if not reals:
            reals.append(Encoding(rules, pattern, real=True, hand=hand))
        return reals[0]

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

    def both(rp, name, extra, limit_int, limit_real):
        """One part with extra conditions on matrix entries: integers, then real numbers."""
        answer, model = solve(enc.part(rp, name) + [f(enc) for f in extra], False, limit_int)
        if answer != 'unknown':
            return answer, model, 'int'
        answer, _ = solve(real().part(rp, name) + [f(real()) for f in extra], True, limit_real)
        # a real solution says nothing about the integers
        return ('unsat' if answer == 'unsat' else 'undecided'), None, 'real'

    parts = []
    for rp, name in enc.parts():
        answer, model, how = both(rp, name, [], t2, t3)
        if answer == 'sat':
            return found(model)
        if answer != 'unsat' and t4:
            # Split on the diagonal: every positive diagonal entry is 1 or at least 2.
            diagonal = enc.diagonal()
            open_ = []
            for combo in itertools.product((False, True), repeat=len(diagonal)):
                fixed = [(lambda e, s=s, i=i, big=big: e.M[s][i][i] >= 2 if big
                          else e.M[s][i][i] == 1) for (s, i), big in zip(diagonal, combo)]
                sub, model, _ = both(rp, name, fixed, t4, t4)
                if sub == 'sat':
                    return found(model)
                # A case that is still open is split once more, on one other entry.
                for s, m in zip(DIGITS, pattern):
                    for i, j in ((0, 1), (1, 0)):
                        if not bit(m, i, j) or sub == 'unsat':
                            continue
                        halves = [both(rp, name, fixed + [extra], t4, t4) for extra in
                                  (lambda e: e.M[s][i][j] == 1, lambda e: e.M[s][i][j] >= 2)]
                        for half in halves:
                            if half[0] == 'sat':
                                return found(half[1])
                        if all(half[0] == 'unsat' for half in halves):
                            sub = 'unsat'
                if sub != 'unsat':
                    open_.append(''.join(f'{s}{i}{">" if big else "="}'
                                         for (s, i), big in zip(diagonal, combo)))
            how = 'split on the diagonal'
            if open_:
                how += ', open: ' + ' '.join(open_)
            else:
                answer = 'unsat'
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
        if form == 'left' and hit:
            # Lemma III holds for this control as well, so requiring a non-zero vector for
            # the digit 2 must not remove its interpretations.
            assert lemma3_applies(rules)
            answer, _ = solve(Encoding(rules, hit[0], hand=True).whole(), False, 60)
            report('the control still has an interpretation under Lemma III', answer == 'sat',
                   answer)

    # 3. Theorems 5, 6 and 8 on concrete matrices.  For digit matrices that satisfy their
    #    hypotheses and for which the weak conditions can be met, z3 (which decides these
    #    small problems) must find the weak conditions satisfiable and no strict rule possible.
    I, M, P = [[1, 0], [0, 1]], [[2, 1], [1, 1]], [[5, 3], [3, 2]]            # P = M*M
    X, U, Z = [[0, 1], [1, 0]], [[1, 1], [1, 1]], [[0, 0], [0, 0]]
    N, NN = [[1, 2], [1, 0]], [[3, 2], [1, 2]]                               # NN = N*N
    instances = [
        ('left', 'f, t = M; 0, 1, 2 = M*M', dict(a=M, b=M, e=P, f=P, g=P)),
        ('left', 'a conjugate of the value representation',
         dict(a=[[5, 1], [3, 7]], b=[[7, 3], [1, 5]], e=[[24, 8], [24, 40]],
              f=[[32, 16], [16, 32]], g=[[40, 24], [8, 24]])),
        ('right', 'all five digits = M', dict(a=M, b=M, e=M, f=M, g=M)),
        ('right', 'f, t = M*M; 0, 1, 2 = M', dict(a=P, b=P, e=M, f=M, g=M)),
        ('right', 'f, t = M; 0, 1, 2 = identity', dict(a=M, b=M, e=I, f=I, g=I)),
        ('left', 'f = 4·identity, t = [[1,1],[12,0]]', dict(
            a=[[4, 0], [0, 4]], b=[[1, 1], [12, 0]], e=[[20, 5], [60, 15]],
            f=[[20, 5], [60, 15]], g=[[20, 5], [60, 15]])),
        ('left', 'f, t = identity; 0, 1, 2 = exchange of the coordinates', dict(
            a=I, b=I, e=[[0, 1], [1, 0]], f=[[0, 1], [1, 0]], g=[[0, 1], [1, 0]])),
        ('right', 'f, t = identity; 0, 1, 2 = exchange of the coordinates', dict(
            a=I, b=I, e=[[0, 1], [1, 0]], f=[[0, 1], [1, 0]], g=[[0, 1], [1, 0]])),
        # Theorem 8
        ('left', 'f, t = exchange of the coordinates; 0, 1, 2 = all entries 1', dict(
            a=X, b=X, e=U, f=U, g=U)),
        ('left', 'f, t = N; 0, 1, 2 = N*N', dict(a=N, b=N, e=NN, f=NN, g=NN)),
        ('left', 'f of rank one, 1 = 9·exchange', dict(
            a=[[1, 2], [1, 2]], b=[[2, 1], [2, 1]], e=[[9, 0], [0, 9]], f=[[0, 9], [9, 0]],
            g=[[9, 0], [0, 9]])),
        ('left', 'a conjugate of the value representation with t and 2 triangular', dict(
            a=[[3, 1], [1, 3]], b=[[4, 2], [0, 2]], e=[[16, 8], [8, 16]],
            f=[[20, 12], [4, 12]], g=[[24, 16], [0, 8]])),
        ('left', 'f upper and t lower triangular', dict(
            a=[[2, 1], [0, 1]], b=[[1, 0], [1, 2]], e=[[9, 6], [0, 3]], f=[[6, 3], [3, 6]],
            g=[[3, 0], [6, 9]])),
        ('right', 'f, t = N; 0, 1, 2 = identity', dict(a=N, b=N, e=I, f=I, g=I)),
        ('right', 'a conjugate of the value representation with t and 2 triangular', dict(
            a=[[6, 2], [2, 6]], b=[[8, 0], [4, 4]], e=[[4, 2], [2, 4]], f=[[5, 1], [3, 3]],
            g=[[6, 0], [4, 2]])),
        ('right', 'f of rank one, 1 = exchange', dict(
            a=[[1, 1], [2, 2]], b=[[2, 2], [1, 1]], e=I, f=X, g=I)),
        ('right', 'f of rank one, 1 = 2·identity', dict(
            a=U, b=[[2, 0], [2, 0]], e=U, f=[[2, 0], [0, 2]], g=[[2, 0], [2, 0]])),
        ('right', 'f upper and t lower triangular', dict(
            a=[[4, 0], [2, 2]], b=[[2, 2], [0, 4]], e=[[3, 0], [2, 1]], f=[[2, 1], [1, 2]],
            g=[[1, 2], [0, 3]])),
        ('right', 'f = exchange, t = identity; 0, 1, 2 = zero', dict(
            a=X, b=I, e=Z, f=Z, g=Z))]
    for form, title, mats in instances:
        rules, _ = parse_problem(systems.COLLATZ.search_problem(form))
        p = tuple(sum(1 << k for k, (i, j) in enumerate(BITS) if mats[s][i][j]) for s in DIGITS)
        covered = by_theorem(p, form) is not None
        enc = Encoding(rules, p, real=True)
        fix = [enc.M[s][i][j] == mats[s][i][j] for s in DIGITS for i, j in BITS]
        weak, _ = solve(enc.constraints + fix + [enc.row[0] + enc.row[1] >= 1], True, 60)
        strict, _ = solve(enc.whole() + fix, True, 60)
        report(f'Theorems 5, 6 and 8 on an instance, {form} form ({title})',
               covered and weak == 'sat' and strict == 'unsat',
               f'covered: {covered}, weak conditions: {weak}, with a strict rule: {strict}')

    # 4. Corollary 10 on concrete matrices of the two kinds it allows: the weak conditions
    #    must stay satisfiable when its condition is added.
    for form, title, mats in [
            ('right', 'a conjugate of the value representation',
             dict(a=[[6, 2], [2, 6]], b=[[8, 0], [4, 4]], e=[[4, 2], [2, 4]],
                  f=[[5, 1], [3, 3]], g=[[6, 0], [4, 2]])),
            ('right', 'f of rank one',
             dict(a=[[1, 1], [2, 2]], b=[[2, 2], [1, 1]], e=I, f=X, g=I)),
            ('left', 'a conjugate of the value representation',
             dict(a=[[3, 1], [1, 3]], b=[[4, 2], [0, 2]], e=[[16, 8], [8, 16]],
                  f=[[20, 12], [4, 12]], g=[[24, 16], [0, 8]])),
            ('left', 'f, t = M; 0, 1, 2 = M*M', dict(a=M, b=M, e=P, f=P, g=P)),
            ('left', 'f upper and t lower triangular',
             dict(a=[[2, 1], [0, 1]], b=[[1, 0], [1, 2]], e=[[9, 6], [0, 3]],
                  f=[[6, 3], [3, 6]], g=[[3, 0], [6, 9]]))]:
        rules, _ = parse_problem(systems.COLLATZ.search_problem(form))
        p = tuple(sum(1 << k for k, (i, j) in enumerate(BITS) if mats[s][i][j]) for s in DIGITS)
        answers = []
        for real in (False, True):
            # only the corollary is added: Lemma III would rightly exclude these matrices in
            # the left form, where Theorems 6 and 8 apply to them
            enc = Encoding(rules, p, real=real)
            fix = [enc.M[s][i][j] == mats[s][i][j] for s in DIGITS for i, j in BITS]
            answers.append(solve(enc.constraints + fix + [enc.corollary10()]
                                 + [enc.row[0] + enc.row[1] >= 1], real, 60)[0])
        report(f'Corollary 10 allows an instance, {form} form ({title})',
               answers == ['sat', 'sat'], f'weak conditions with the corollary: {answers}')
    return ok


# ---------------------------------------------------------------------------------------

def work(job):
    form, p, t1, t2, t3, t4, hand = job
    start = time.time()
    verdict, detail = decide(systems.COLLATZ.search_problem(form), tuple(p), t1, t2, t3, t4,
                             hand)
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
    if args.hand:
        # second pass: the patterns that the first pass left undecided
        todo = [p for p in todo if p in done and done[p]['verdict'] == 'undecided']
        path = os.path.join(args.out, f'{args.form}-hand.jsonl')
        done = load(path)
    if args.again:
        todo = [p for p in todo if p in done and done[p]['verdict'] == 'undecided']
    else:
        todo = [p for p in todo if p not in done]
    print(f'{args.form} form{", second pass" if args.hand else ""}: {len(done)} patterns '
          f'recorded, {len(todo)} to do', flush=True)
    jobs = [(args.form, p, args.t1, args.t2, args.t3, args.t4, args.hand) for p in todo]
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
           'First pass, z3 alone (with Lemmas I and II):',
           '',
           '- "none": z3 refuted every part of the case.',
           '- "found": z3 produced an interpretation and `checker/check.py` accepted it.',
           '- "undecided": z3 gave no answer within the time limits for at least one part.',
           '',
           'Second pass, for the patterns undecided in the first:',
           '',
           '- "Theorem 6", "Theorem 8": the written theorem excludes every interpretation with',
           '  the pattern; no solver is involved. A pattern that both theorems exclude is',
           '  counted under Theorem 6.',
           '- "z3 again": z3 refuted the pattern with the extra split on the values of matrix',
           '  entries and with the conditions of Lemma III (left form) and Lemma IV.',
           '',
           '| Form | Patterns | None, first pass | Theorem 6 | Theorem 8 | z3 again | Found | '
           'Undecided |',
           '|---|---|---|---|---|---|---|---|']
    details = []
    for form in ('left', 'right'):
        path = os.path.join(args.out, f'{form}.jsonl')
        if not os.path.exists(path):
            continue
        rs = list(load(path).values())
        second = load(os.path.join(args.out, f'{form}-hand.jsonl'))
        count = lambda v, c=None: sum(1 for r in rs if r['verdict'] == v
                                      and (c is None or r['class'] == c))

        def kind(r):
            """How a pattern undecided in the first pass ended."""
            h = second.get(tuple(r['pattern']))
            if h is None or h['verdict'] == 'undecided':
                return 'undecided'
            if h['verdict'] == 'found':
                return 'found'
            how = h['detail']['how']
            return how if how in ('theorem 6', 'theorem 8') else 'z3 again'

        open_ = [r for r in rs if r['verdict'] == 'undecided']
        kinds = {tuple(r['pattern']): kind(r) for r in open_}
        ends = lambda k, c=None: sum(1 for r in open_ if kinds[tuple(r['pattern'])] == k
                                     and (c is None or r['class'] == c))
        found = count('found') + ends('found')
        out.append(f'| {form} | {len(rs):,} | {count("none"):,} | {ends("theorem 6")} | '
                   f'{ends("theorem 8")} | {ends("z3 again")} | {found} | '
                   f'{ends("undecided")} |')
        details += ['', f'## {form.capitalize()} form', '',
                    '| Kind of pattern | Patterns | None, first pass | Theorem 6 | Theorem 8 | '
                    'z3 again | Found | Undecided |',
                    '|---|---|---|---|---|---|---|---|']
        for c in ('irreducible', 'triangular', 'diagonal'):
            n = sum(1 for r in rs if r['class'] == c)
            details.append(f'| {c} | {n:,} | {count("none", c):,} | {ends("theorem 6", c)} | '
                           f'{ends("theorem 8", c)} | {ends("z3 again", c)} | '
                           f'{count("found", c) + ends("found", c)} | {ends("undecided", c)} |')
        whole = sum(1 for r in rs if r['verdict'] == 'none' and r['detail']['how'] == 'whole')
        split = [r for r in rs if r['verdict'] == 'none' and r['detail']['how'] == 'parts']
        with_real = sum(1 for r in split if any(x[3] == 'real' for x in r['detail']['parts']))
        again = [second[p] for p in kinds if kinds[p] == 'z3 again']
        with_diag = sum(1 for r in again if r['detail']['how'] == 'parts'
                        and any(x[3].startswith('split') for x in r['detail']['parts']))
        details += ['',
                    f'First pass: {whole:,} patterns refuted as one integer problem, '
                    f'{len(split)} after splitting, of which {with_real} needed the '
                    'real-number procedure for at least one part.']
        if again:
            details += ['', f'Second pass: of the {len(again)} patterns refuted by z3, '
                        f'{with_diag} needed the split on the values of matrix entries.']
        # The theorems against the first pass: the two must never contradict each other.
        for name, test in (('Theorem 6', theorem6), ('Theorem 8', lambda p: theorem8(p, form))):
            covered = [r for r in rs if test(tuple(r['pattern']))]
            details += ['',
                        f'{name} covers {len(covered):,} patterns in all. In the first pass '
                        f'z3 refuted {sum(1 for r in covered if r["verdict"] == "none"):,} of '
                        f'them, left {sum(1 for r in covered if r["verdict"] == "undecided")} '
                        f'undecided and found an interpretation for '
                        f'{sum(1 for r in covered if r["verdict"] == "found")}.']
        both = sum(1 for r in rs if by_theorem(tuple(r['pattern']), form))
        details += ['', f'Together the two theorems cover {both:,} of the {len(rs):,} '
                    'patterns.']
        still = [r for r in open_ if kinds[tuple(r['pattern'])] == 'undecided']
        if still:
            details += ['', 'Undecided patterns (entries of each digit matrix that may be '
                        'non-zero, as a 4-bit number: 1 top left, 2 top right, 4 bottom left, '
                        '8 bottom right; order f, t, 0, 1, 2):', '']
            details += [f'- `{r["pattern"]}` ({r["class"]})' for r in still]
        for r in rs + list(second.values()):
            if r['verdict'] == 'found':
                details += ['', f'Found for pattern `{r["pattern"]}`: '
                            + json.dumps(r['detail']['certificate'])]
    out += details
    with open(os.path.join(args.out, 'summary.md'), 'w') as f:
        f.write('\n'.join(out) + '\n')
    print('\n'.join(out[25:]))


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
                    help='seconds per case when an undecided part is split on the values of '
                         'matrix entries (0: no splitting)')
    ap.add_argument('--again', action='store_true',
                    help='re-run the patterns recorded as undecided (with other time limits)')
    ap.add_argument('--hand', action='store_true',
                    help='second pass over the patterns undecided in the first, using '
                         'the lemmas and theorems of docs/dimension2.md')
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
