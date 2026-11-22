#!/usr/bin/env python3
"""Independent checker for matrix-interpretation termination certificates.

This file shares no code with any prover.  It uses only Python integers (exact arithmetic,
no numpy, no floating point) and re-derives every inequality from the symbol interpretations.

What is checked
---------------
A *problem* is a string rewriting system given as lines `lhs ARROW rhs`:

    ->     strict rule, may be applied anywhere in a string
    ->=    weak rule, may be applied anywhere
    |->    strict rule, may be applied only at the left end of a string ("top" rule)

If a problem has top rules it is a relative *top* termination problem, SN(R_top / S): no
infinite rewrite sequence uses the strict rules R infinitely often when R is applied only at
the left end and the weak rules S anywhere.  Otherwise it is a relative termination problem,
SN(R / S).

A *certificate* is a list of steps.  Each step interprets every symbol s as an affine map
[s](x) = M_s x + v_s and names the strict rules it removes.  A step is valid when

  * the maps form a weakly monotone algebra (top problems) or an extended monotone algebra
    (other problems) -- see `check_algebra`;
  * every rule still present satisfies [lhs] >= [rhs]  (elementwise on M and v);
  * every rule it removes satisfies [lhs] > [rhs]      (the strict order of that algebra).

The certificate is accepted when, after all steps, no strict rule is left.  The conditions are
those of Endrullis, Waldmann & Zantema (2008, natural numbers) and Koprowski & Waldmann
(2009, arctic numbers), as stated in Sections 2.2-2.3 of Yolcu, Aaronson & Heule (2023).

Conventions
-----------
A string s1 s2 ... sn is interpreted as the composition [s1] o [s2] o ... o [sn], so the
leftmost symbol is the outermost function.  In arctic certificates -infinity is JSON `null`.

Usage:  check.py PROBLEM.srs CERTIFICATE.json
"""
import json
import sys
from collections import namedtuple

Rule = namedtuple('Rule', 'left right strict top')
NEG_INF = None


class CertificateError(Exception):
    pass


# ---------------------------------------------------------------------------------------
# Problems
# ---------------------------------------------------------------------------------------

def parse_problem(text):
    rules = []
    for raw in text.splitlines():
        line = raw.split('//')[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 3:
            raise CertificateError(f'cannot parse rule: {raw!r}')
        left, arrow, right = parts
        if arrow == '->':
            strict, top = True, False
        elif arrow == '->=':
            strict, top = False, False
        elif arrow == '|->':
            strict, top = True, True
        else:
            raise CertificateError(f'unsupported arrow {arrow!r} in {raw!r}')
        rules.append(Rule(tuple(left), tuple(right), strict, top))
    if not rules:
        raise CertificateError('empty problem')
    is_top = any(r.top for r in rules)
    if is_top and any(r.strict and not r.top for r in rules):
        raise CertificateError('a top termination problem cannot have strict non-top rules')
    return rules, is_top


def rule_str(r):
    arrow = ('|' if r.top else '') + ('->' if r.strict else '->=')
    return f'{"".join(r.left)} {arrow} {"".join(r.right)}'


# ---------------------------------------------------------------------------------------
# The two semirings
# ---------------------------------------------------------------------------------------

class Natural:
    """(N, +, *).  x > y is the usual order; vectors compare strictly on the first entry."""
    name = 'natural'
    zero = 0

    @staticmethod
    def valid(x):
        return isinstance(x, int) and not isinstance(x, bool) and x >= 0

    @staticmethod
    def add(x, y):
        return x + y

    @staticmethod
    def mul(x, y):
        return x * y

    @staticmethod
    def ge(x, y):
        return x >= y

    @staticmethod
    def check_algebra(sym, M, v, extended):
        if extended and not M[0][0] >= 1:
            raise CertificateError(f'[{sym}] is not strictly monotone: M[1][1] must be >= 1')

    @staticmethod
    def weak(LM, Lv, RM, Rv):
        return _all_pairs(Natural.ge, LM, RM) and all(map(Natural.ge, Lv, Rv))

    @staticmethod
    def strict(LM, Lv, RM, Rv):
        return Natural.weak(LM, Lv, RM, Rv) and Lv[0] > Rv[0]


class Arctic:
    """(Z u {-inf}, max, +).  x >> y means x > y, or x = y = -inf."""
    name = 'arctic'
    zero = NEG_INF

    @staticmethod
    def valid(x):
        return x is NEG_INF or (isinstance(x, int) and not isinstance(x, bool))

    @staticmethod
    def add(x, y):
        if x is NEG_INF:
            return y
        if y is NEG_INF:
            return x
        return max(x, y)

    @staticmethod
    def mul(x, y):
        if x is NEG_INF or y is NEG_INF:
            return NEG_INF
        return x + y

    @staticmethod
    def ge(x, y):
        if y is NEG_INF:
            return True
        if x is NEG_INF:
            return False
        return x >= y

    @staticmethod
    def gg(x, y):
        if x is NEG_INF:
            return y is NEG_INF
        if y is NEG_INF:
            return True
        return x > y

    @staticmethod
    def check_algebra(sym, M, v, extended):
        finite_nonneg = lambda x: x is not NEG_INF and x >= 0
        if extended:
            # Extended monotone algebra: arctic naturals only, no constant part.
            if any(x is not NEG_INF for x in v):
                raise CertificateError(f'[{sym}] must have v = -inf for full termination')
            if any(x is not NEG_INF and x < 0 for row in M for x in row):
                raise CertificateError(f'[{sym}] uses negative entries in full termination')
            if not finite_nonneg(M[0][0]):
                raise CertificateError(f'[{sym}]: M[1][1] must be finite and >= 0')
        elif not (finite_nonneg(M[0][0]) or finite_nonneg(v[0])):
            # Needed so that [s] maps N x A^(d-1) into itself.
            raise CertificateError(f'[{sym}]: need M[1][1] >= 0 or v[1] >= 0')

    @staticmethod
    def weak(LM, Lv, RM, Rv):
        return _all_pairs(Arctic.ge, LM, RM) and all(map(Arctic.ge, Lv, Rv))

    @staticmethod
    def strict(LM, Lv, RM, Rv):
        return _all_pairs(Arctic.gg, LM, RM) and all(map(Arctic.gg, Lv, Rv))


SEMIRINGS = {'natural': Natural, 'arctic': Arctic}


def _all_pairs(rel, A, B):
    return all(rel(a, b) for ra, rb in zip(A, B) for a, b in zip(ra, rb))


def compose(S, outer, inner):
    """(M1, v1) o (M2, v2) = (M1 M2, M1 v2 + v1), in semiring S."""
    M1, v1 = outer
    M2, v2 = inner
    d = len(M1)
    M = [[S.zero] * d for _ in range(d)]
    v = [S.zero] * d
    for i in range(d):
        for j in range(d):
            acc = S.zero
            for k in range(d):
                acc = S.add(acc, S.mul(M1[i][k], M2[k][j]))
            M[i][j] = acc
        acc = v1[i]
        for k in range(d):
            acc = S.add(acc, S.mul(M1[i][k], v2[k]))
        v[i] = acc
    return M, v


def interpret(S, string, interp):
    out = interp[string[0]]
    for sym in string[1:]:
        out = compose(S, out, interp[sym])
    return out


# ---------------------------------------------------------------------------------------
# Certificates
# ---------------------------------------------------------------------------------------

def load_step(step, symbols):
    kind = step.get('type')
    if kind not in SEMIRINGS:
        raise CertificateError(f'unknown interpretation type {kind!r}')
    S = SEMIRINGS[kind]
    d = step.get('dimension')
    if not isinstance(d, int) or d < 1:
        raise CertificateError('bad dimension')
    interp = {}
    for sym in symbols:
        entry = step['interpretation'].get(sym)
        if entry is None:
            raise CertificateError(f'no interpretation for symbol {sym!r}')
        M, v = entry['M'], entry['v']
        if len(M) != d or any(len(row) != d for row in M) or len(v) != d:
            raise CertificateError(f'[{sym}] has the wrong shape')
        if not all(S.valid(x) for row in M for x in row) or not all(S.valid(x) for x in v):
            raise CertificateError(f'[{sym}] has an entry outside the {kind} semiring')
        interp[sym] = ([list(row) for row in M], list(v))
    return S, interp


def check(problem_text, certificate, log=None, allow_partial=False):
    """Return a summary dict, or raise CertificateError.

    With `allow_partial`, a certificate whose steps are all valid but which leaves strict
    rules behind is not rejected; the rules left are reported under 'remaining_strict'.
    """
    say = log if log is not None else (lambda *_: None)
    rules, is_top = parse_problem(problem_text)
    remaining = list(rules)
    steps = certificate.get('steps')
    if not isinstance(steps, list):
        raise CertificateError('certificate has no steps')

    summary = []
    for n, step in enumerate(steps, 1):
        symbols = sorted({s for r in remaining for s in r.left + r.right})
        S, interp = load_step(step, symbols)
        for sym in symbols:
            S.check_algebra(sym, *interp[sym], extended=not is_top)

        by_name = {rule_str(r): r for r in remaining}
        to_remove = []
        for name in step.get('removed', []):
            if name not in by_name:
                raise CertificateError(f'step {n} removes {name!r}, which is not a remaining rule')
            to_remove.append(by_name[name])
        if not to_remove:
            raise CertificateError(f'step {n} removes nothing')

        for r in remaining:
            L = interpret(S, r.left, interp)
            R = interpret(S, r.right, interp)
            if not S.weak(*L, *R):
                raise CertificateError(f'step {n}: {rule_str(r)} is not weakly decreasing')
            if r in to_remove:
                if not r.strict:
                    raise CertificateError(f'step {n}: {rule_str(r)} is a weak rule')
                if not S.strict(*L, *R):
                    raise CertificateError(f'step {n}: {rule_str(r)} is not strictly decreasing')
        remaining = [r for r in remaining if r not in to_remove]
        say(f'step {n}: {S.name}, dimension {step["dimension"]}, '
            f'removes {", ".join(rule_str(r) for r in to_remove)}')
        summary.append({'type': S.name, 'dimension': step['dimension'],
                        'removed': [rule_str(r) for r in to_remove]})

    left = [rule_str(r) for r in remaining if r.strict]
    if left and not allow_partial:
        raise CertificateError('strict rules remain after the last step: ' + ', '.join(left))
    return {'kind': 'relative top termination' if is_top else 'relative termination',
            'remaining_strict': left,
            'strict_rules': [rule_str(r) for r in rules if r.strict],
            'weak_rules': [rule_str(r) for r in rules if not r.strict],
            'steps': summary}


def main(argv):
    if len(argv) != 3:
        sys.exit(__doc__.split('Usage:')[1].strip().join(['usage: ', '']))
    with open(argv[1]) as f:
        problem = f.read()
    with open(argv[2]) as f:
        certificate = json.load(f)
    try:
        result = check(problem, certificate, log=print)
    except CertificateError as e:
        print(f'REJECTED: {e}')
        return 1
    print(f'ACCEPTED: {result["kind"]} of {len(result["strict_rules"])} strict rule(s) '
          f'relative to {len(result["weak_rules"])} weak rule(s)')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
