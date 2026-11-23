#!/usr/bin/env python3
"""Check Theorem 7 of docs/dimension2.md on every small example.

Theorem 7 describes the 2x2 matrices A, B, E, F, G with non-negative integer entries that
satisfy the six carry equalities

    A E = E A    A F = E B    A G = F A    B E = F B    B F = G A    B G = G B

when both entries off the diagonal of A are positive: one of the cases (S0) to (S3) of the
theorem holds.  This script lists every solution with entries up to a bound, tests the four
cases directly from their statements, and counts.  It also tests the step of Theorem 8 (left
form) that follows: whenever a non-zero row r >= 0 satisfies the matrix parts of the three
rules for the left end marker, there is a positive row that is a left eigenvector of B and of
G with a larger eigenvalue for G, or all five matrices are permutation matrices and r has two
equal entries.

A check, not a proof: it covers the entries 0..bound only, and it uses floating point for
the eigenvectors.

Usage:  theorem7_check.py [--bound 3]
"""
import argparse
import sys

import numpy as np

TOL = 1e-7


def perron(M):
    """Spectral radius and a positive eigenvector (column) of an irreducible 2x2 matrix."""
    values, vectors = np.linalg.eig(M.astype(float))
    i = int(np.argmax(values.real))
    v = vectors[:, i].real
    return values[i].real, (v if v.sum() > 0 else -v)


def eigenvalue(row, M):
    """c with row·M = c·row, or None."""
    image = row @ M
    k = int(np.argmax(np.abs(row)))
    c = image[k] / row[k]
    return c if np.allclose(image, c * row, atol=TOL) else None


def classify(A, B, E, F, G):
    """The set of cases of Theorem 7 that hold."""
    det = int(round(np.linalg.det(A)))
    alpha, x = perron(A)
    _, y = perron(A.T)
    eps = eigenvalue(y, E)
    assert eps is not None                          # E commutes with A
    cases = set()
    if not F.any() and not G.any():
        cases.add('S0')
    left = [eigenvalue(y, M) for M in (B, F, G)]
    right = [eigenvalue(x, M.T) for M in (B, E, F, G)]
    if None not in left and None not in right and np.allclose(left, [alpha, eps, eps], atol=TOL) \
            and np.allclose(right, [alpha, eps, eps, eps], atol=TOL):
        cases.add('S1')
    if det > 0 and None not in left and np.allclose(left, [alpha, eps, eps], atol=TOL):
        for M in (A, B):
            values = sorted(np.linalg.eigvals(M.astype(float)).real)
            if not np.allclose(values, [alpha / 2, alpha], atol=TOL):
                break
        else:
            cases.add('S2')
    if det == 0 and eps > TOL and np.allclose(F @ x, eps * x, atol=TOL):
        for row in (y, y @ F):
            if row.min() > TOL and np.allclose(row @ B, alpha * row, atol=TOL) \
                    and np.allclose(row @ G, eps * row, atol=TOL):
                cases.add('S3')
    return cases


def rows_for_left_marker(A, B, E, F, G):
    """Non-zero rows r >= 0 with rE >= rB, rF >= rAA, rG >= rAB: generators of that cone."""
    columns = np.concatenate([(E - B).T, (F - A @ A).T, (G - A @ B).T, np.eye(2)]).astype(float)
    candidates = [np.array([1.0, 0.0]), np.array([0.0, 1.0])]
    for c in columns:
        candidates += [np.array([c[1], -c[0]]), np.array([-c[1], c[0]])]
    return [r / np.abs(r).max() for r in candidates
            if np.abs(r).max() > 0 and (columns @ r >= -TOL).all()]


def theorem8_left(A, B, E, F, G, rows):
    """'larger' | 'permutation' | None for a solution that admits a row r."""
    alpha, x = perron(A)
    _, y = perron(A.T)
    for row in (y, y @ F):
        if row.min() <= TOL:
            continue
        beta, gamma = eigenvalue(row, B), eigenvalue(row, G)
        if beta is not None and gamma is not None and abs(beta - alpha) < TOL \
                and gamma > beta + TOL and gamma >= 1 - TOL:
            return 'larger'
    permutations = all(sorted(M.flatten().tolist()) == [0, 0, 1, 1]
                       and M.sum(axis=0).tolist() == [1, 1] for M in (A, B, E, F, G))
    if permutations and all(abs(r[0] - r[1]) < TOL for r in rows):
        return 'permutation'
    return None


def solutions(bound):
    values = range(bound + 1)
    ALL = np.array([[[a, b], [c, d]] for a in values for b in values for c in values
                    for d in values])
    same = lambda X, Y: (X == Y).all(axis=(1, 2))
    for A in ALL:
        if not (A[0, 1] > 0 and A[1, 0] > 0):
            continue
        AX = np.einsum('ij,njk->nik', A, ALL)
        XA = np.einsum('nij,jk->nik', ALL, A)
        for E in ALL[same(AX, XA)]:
            for B in ALL:
                XB = np.einsum('nij,jk->nik', ALL, B)
                BX = np.einsum('ij,njk->nik', B, ALL)
                for F in ALL[same(AX, E @ B) & same(XB, B @ E)]:
                    for G in ALL[same(AX, F @ A) & same(XA, B @ F) & same(BX, XB)]:
                        yield A, B, E, F, G


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--bound', type=int, default=3)
    args = ap.parse_args()
    counts, failures = {}, []

    def count(key):
        counts[key] = counts.get(key, 0) + 1

    # An example of case (S2) needs larger entries than the bound; it is tested separately.
    example = [np.array(M) for M in ([[3, 1], [1, 3]], [[4, 2], [0, 2]], [[4, 2], [2, 4]],
                                     [[5, 3], [1, 3]], [[6, 4], [0, 2]])]
    A, B, E, F, G = example
    assert all((X == Y).all() for X, Y in ((A @ E, E @ A), (A @ F, E @ B), (A @ G, F @ A),
                                           (B @ E, F @ B), (B @ F, G @ A), (B @ G, G @ B)))
    if classify(*example) != {'S2'}:
        failures.append(('the example for (S2)', example))

    for solution in solutions(args.bound):
        A = solution[0]
        det = int(round(np.linalg.det(A)))
        sign = 'negative' if det < 0 else 'zero' if det == 0 else 'positive'
        cases = classify(*solution)
        if not cases:
            failures.append(('no case of Theorem 7', solution))
        for c in cases or {'none'}:
            count((sign, c))
        count((sign, 'solutions'))
        rows = rows_for_left_marker(*solution)
        if rows:
            kind = theorem8_left(*solution, rows)
            count((sign, 'row: ' + str(kind)))
            if kind is None or 'S0' in cases:
                failures.append(('step of Theorem 8', solution))

    print(f'Entries 0..{args.bound}, both entries off the diagonal of A positive.')
    print()
    print('| det A | Solutions | (S0) | (S1) | (S2) | (S3) | None | '
          'Admit a row r | G larger than B | Permutations |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    for sign in ('negative', 'zero', 'positive'):
        get = lambda k: counts.get((sign, k), 0)
        print(f'| {sign} | {get("solutions"):,} | {get("S0"):,} | {get("S1"):,} | {get("S2")} | '
              f'{get("S3")} | {get("none")} | {get("row: larger") + get("row: permutation")} | '
              f'{get("row: larger")} | {get("row: permutation")} |')
    print()
    print('The example for (S2) is classified as (S2):',
          not any(f[0] == 'the example for (S2)' for f in failures))
    print('Failures:', len(failures))
    for name, solution in failures[:10]:
        print(' ', name, [M.tolist() for M in solution])
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
