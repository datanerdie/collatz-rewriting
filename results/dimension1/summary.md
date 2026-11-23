# Dimension 1 with unbounded coefficients

Produced by `harness/dimension1.py` with z3 5.4.1.
For each problem: is there a one-dimensional interpretation, with integer
coefficients of any size, that makes every rule weakly decreasing and at least one
strict rule strictly decreasing?

- "none": z3 reports that no such interpretation exists. For natural interpretations
  this is a statement about every weakly monotone affine function on the natural
  numbers. It rests on z3; for the system T there is also a written proof in
  `docs/dimension1.md`.
- "found": z3 produced one and `checker/check.py` accepted it; the rules it removes
  are listed (as written in the problem file, reversed in the right form).
- "unknown": z3 did not decide within 120 seconds.
- Arctic interpretations here may have entries below zero, which Phase 3 did not
  search.

## The Collatz conjecture itself

| Problem | Rules | Natural | Arctic |
|---|---|---|---|
| T.left | 11 | none | none |
| T.right | 11 | none | none |
| S.left | 15 | none | none |
| S.right | 15 | none | none |
| S2.left | 18 | none | none |
| S2.right | 18 | none | none |
| T.c2.left | 12 | none | none |
| T.c2.right | 12 | none | none |
| S.c2.left | 16 | none | none |
| S.c2.right | 16 | none | none |
| T.c3.left | 14 | none | none |
| T.c3.right | 14 | none | none |
| S.c3.left | 18 | none | none |
| S.c3.right | 18 | none | none |
| T.k2.left | 13 | none | none |
| T.k2.right | 13 | none | none |
| S.k2.left | 16 | none | none |
| S.k2.right | 16 | none | none |
| T.k3.left | 17 | none | none |
| T.k3.right | 17 | none | none |
| S.k3.left | 20 | none | none |
| S.k3.right | 20 | none | none |
| T.k4.left | 25 | none | none |
| T.k4.right | 25 | none | none |
| S.k4.left | 28 | none | none |
| S.k4.right | 28 | none | none |
| T.k5.left | 41 | none | none |
| T.k5.right | 41 | none | none |
| S.k5.left | 44 | none | none |
| S.k5.right | 44 | unknown | none |
| T.k6.left | 73 | none | none |
| T.k6.right | 73 | unknown | none |
| S.k6.left | 76 | none | none |
| S.k6.right | 76 | unknown | none |

## Negative controls: systems that loop

| Problem | Rules | Natural | Arctic |
|---|---|---|---|
| T-.left | 11 | none | none |
| T-.right | 11 | none | none |
| S-.left | 11 | none | none |
| S-.right | 11 | none | none |
| T5.left | 17 | none | none |
| T5.right | 17 | none | none |
| T-.k2.left | 13 | none | none |
| T-.k2.right | 13 | none | none |
| S-.k2.left | 13 | none | none |
| S-.k2.right | 13 | none | none |
| T5.k2.left | 19 | none | none |
| T5.k2.right | 19 | none | none |
| T-.k3.left | 17 | none | none |
| T-.k3.right | 17 | none | none |
| S-.k3.left | 17 | none | none |
| S-.k3.right | 17 | none | none |
| T5.k3.left | 23 | none | none |
| T5.k3.right | 23 | none | none |
| T-.k4.left | 25 | none | none |
| T-.k4.right | 25 | unknown | none |
| S-.k4.left | 25 | none | none |
| S-.k4.right | 25 | none | none |
| T5.k4.left | 31 | none | none |
| T5.k4.right | 31 | none | none |

## Targets: statements the paper leaves open

| Problem | Rules | Natural | Arctic |
|---|---|---|---|
| T.c3-no1mod8.left | 13 | none | none |
| T.c3-no1mod8.right | 13 | none | none |
| S.c3-no1mod8.left | 17 | none | none |
| S.c3-no1mod8.right | 17 | none | none |
| T.k3-no1mod8.left | 16 | none | none |
| T.k3-no1mod8.right | 16 | none | none |
| S.k3-no1mod8.left | 19 | none | none |
| S.k3-no1mod8.right | 19 | none | none |
| T.c3-no5mod8.left | 13 | none | none |
| T.c3-no5mod8.right | 13 | none | none |
| S.c3-no5mod8.left | 17 | none | none |
| S.c3-no5mod8.right | 17 | none | none |
| T.k3-no5mod8.left | 16 | none | none |
| T.k3-no5mod8.right | 16 | none | none |
| S.k3-no5mod8.left | 19 | none | none |
| S.k3-no5mod8.right | 19 | none | none |
| T.c3-no7mod8.left | 13 | none | none |
| T.c3-no7mod8.right | 13 | none | none |
| S.c3-no7mod8.left | 17 | none | found, removes `ci |-> ca` |
| S.c3-no7mod8.right | 17 | none | none |
| T.k3-no7mod8.left | 16 | none | none |
| T.k3-no7mod8.right | 16 | unknown | none |
| S.k3-no7mod8.left | 19 | none | none |
| S.k3-no7mod8.right | 19 | none | none |
| T.c3-no5or7mod8.left | 12 | none | none |
| T.c3-no5or7mod8.right | 12 | none | none |
| S.c3-no5or7mod8.left | 16 | none | found, removes `ci |-> ca` |
| S.c3-no5or7mod8.right | 16 | none | none |
| T.k3-no5or7mod8.left | 15 | none | none |
| T.k3-no5or7mod8.right | 15 | unknown | none |
| S.k3-no5or7mod8.left | 18 | none | none |
| S.k3-no5or7mod8.right | 18 | none | none |

## Controls: statements the paper proved

| Problem | Rules | Natural | Arctic |
|---|---|---|---|
| T.c2-no1mod4.left | 11 | none | none |
| T.c2-no1mod4.right | 11 | none | none |
| S.c2-no1mod4.left | 15 | none | none |
| S.c2-no1mod4.right | 15 | found, removes `dbb |-> dai` | found, removes `dbb |-> dai` |
| T.k2-no1mod4.left | 12 | none | none |
| T.k2-no1mod4.right | 12 | none | none |
| S.k2-no1mod4.left | 15 | none | none |
| S.k2-no1mod4.right | 15 | none | none |
| T.c2-no3mod4.left | 11 | none | found, removes `ce |-> cb` |
| T.c2-no3mod4.right | 11 | none | none |
| S.c2-no3mod4.left | 15 | none | found, removes `ci |-> ca` |
| S.c2-no3mod4.right | 15 | none | none |
| T.k2-no3mod4.left | 12 | found, removes `ce |-> cb` | found, removes `ce |-> cb` |
| T.k2-no3mod4.right | 12 | found, removes `daa |-> d`, `dba |-> df`, `dab |-> dg` | found, removes `daa |-> d` |
| S.k2-no3mod4.left | 15 | none | none |
| S.k2-no3mod4.right | 15 | found, removes `dba |-> di`, `dab |-> dg`, `dbb |-> dei` | none |
| T.c3-no3mod8.left | 13 | none | none |
| T.c3-no3mod8.right | 13 | none | none |
| S.c3-no3mod8.left | 17 | none | none |
| S.c3-no3mod8.right | 17 | none | none |
| T.k3-no3mod8.left | 16 | none | none |
| T.k3-no3mod8.right | 16 | none | none |
| S.k3-no3mod8.left | 19 | none | none |
| S.k3-no3mod8.right | 19 | none | none |
| T.c3-no1or5mod8.left | 12 | none | none |
| T.c3-no1or5mod8.right | 12 | none | none |
| S.c3-no1or5mod8.left | 16 | none | none |
| S.c3-no1or5mod8.right | 16 | found, removes `dbb |-> dai` | found, removes `dbb |-> dai` |
| T.k3-no1or5mod8.left | 15 | none | none |
| T.k3-no1or5mod8.right | 15 | none | none |
| S.k3-no1or5mod8.left | 18 | none | none |
| S.k3-no1or5mod8.right | 18 | none | none |
| T.c3-no1or7mod8.left | 12 | none | none |
| T.c3-no1or7mod8.right | 12 | none | none |
| S.c3-no1or7mod8.left | 16 | none | found, removes `ci |-> ca` |
| S.c3-no1or7mod8.right | 16 | none | none |
| T.k3-no1or7mod8.left | 15 | none | none |
| T.k3-no1or7mod8.right | 15 | unknown | none |
| S.k3-no1or7mod8.left | 18 | none | none |
| S.k3-no1or7mod8.right | 18 | none | none |

## Totals

| Group | Type | None | Found | Unknown |
|---|---|---|---|---|
| full | natural | 31 | 0 | 3 |
| full | arctic | 34 | 0 | 0 |
| negative | natural | 23 | 0 | 1 |
| negative | arctic | 24 | 0 | 0 |
| target | natural | 30 | 0 | 2 |
| target | arctic | 30 | 2 | 0 |
| control | natural | 34 | 5 | 1 |
| control | arctic | 33 | 7 | 0 |
