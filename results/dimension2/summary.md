# Dimension 2 with unbounded coefficients: case analysis for the system T

Produced by `harness/dimension2.py` with z3 5.4.1.
The method and the proofs it relies on are in `docs/dimension2.md`.

For each zero pattern of the five digit matrices: is there a two-dimensional natural
interpretation with that pattern under which every rule of T is weakly decreasing
and some strict rule is strictly decreasing?

First pass, z3 alone (with Lemmas I and II):

- "none": z3 refuted every part of the case.
- "found": z3 produced an interpretation and `checker/check.py` accepted it.
- "undecided": z3 gave no answer within the time limits for at least one part.

Second pass, for the patterns undecided in the first:

- "Theorem 6", "Theorem 8": the written theorem excludes every interpretation with
  the pattern; no solver is involved. A pattern that both theorems exclude is
  counted under Theorem 6.
- "z3 again": z3 refuted the pattern with the extra split on the values of matrix
  entries and with the conditions of Lemma III (left form) and Lemma IV.

| Form | Patterns | None, first pass | Theorem 6 | Theorem 8 | z3 again | Found | Undecided |
|---|---|---|---|---|---|---|---|
| left | 7,495 | 7,350 | 96 | 26 | 17 | 0 | 6 |
| right | 7,495 | 7,318 | 94 | 24 | 15 | 0 | 44 |

## Left form

| Kind of pattern | Patterns | None, first pass | Theorem 6 | Theorem 8 | z3 again | Found | Undecided |
|---|---|---|---|---|---|---|---|
| irreducible | 4,955 | 4,832 | 96 | 26 | 1 | 0 | 0 |
| triangular | 2,435 | 2,413 | 0 | 0 | 16 | 0 | 6 |
| diagonal | 105 | 105 | 0 | 0 | 0 | 0 | 0 |

First pass: 7,321 patterns refuted as one integer problem, 29 after splitting, of which 3 needed the real-number procedure for at least one part.

Second pass: of the 17 patterns refuted by z3, 3 needed the split on the values of matrix entries.

Theorem 6 covers 1,043 patterns in all. In the first pass z3 refuted 947 of them, left 96 undecided and found an interpretation for 0.

Theorem 8 covers 1,512 patterns in all. In the first pass z3 refuted 1,400 of them, left 112 undecided and found an interpretation for 0.

Together the two theorems cover 1,873 of the 7,495 patterns.

Undecided patterns (entries of each digit matrix that may be non-zero, as a 4-bit number: 1 top left, 2 top right, 4 bottom left, 8 bottom right; order f, t, 0, 1, 2):

- `[1, 11, 3, 3, 11]` (triangular)
- `[3, 11, 3, 3, 3]` (triangular)
- `[3, 11, 3, 3, 11]` (triangular)
- `[9, 11, 3, 3, 3]` (triangular)
- `[11, 11, 3, 3, 3]` (triangular)
- `[11, 11, 11, 11, 11]` (triangular)

## Right form

| Kind of pattern | Patterns | None, first pass | Theorem 6 | Theorem 8 | z3 again | Found | Undecided |
|---|---|---|---|---|---|---|---|
| irreducible | 4,955 | 4,835 | 94 | 24 | 2 | 0 | 0 |
| triangular | 2,435 | 2,378 | 0 | 0 | 13 | 0 | 44 |
| diagonal | 105 | 105 | 0 | 0 | 0 | 0 | 0 |

First pass: 7,308 patterns refuted as one integer problem, 10 after splitting, of which 3 needed the real-number procedure for at least one part.

Second pass: of the 15 patterns refuted by z3, 9 needed the split on the values of matrix entries.

Theorem 6 covers 1,043 patterns in all. In the first pass z3 refuted 949 of them, left 94 undecided and found an interpretation for 0.

Theorem 8 covers 1,512 patterns in all. In the first pass z3 refuted 1,403 of them, left 109 undecided and found an interpretation for 0.

Together the two theorems cover 1,873 of the 7,495 patterns.

Undecided patterns (entries of each digit matrix that may be non-zero, as a 4-bit number: 1 top left, 2 top right, 4 bottom left, 8 bottom right; order f, t, 0, 1, 2):

- `[3, 3, 1, 1, 3]` (triangular)
- `[3, 3, 1, 1, 11]` (triangular)
- `[3, 3, 1, 3, 3]` (triangular)
- `[3, 3, 1, 3, 11]` (triangular)
- `[3, 3, 1, 9, 3]` (triangular)
- `[3, 3, 1, 9, 11]` (triangular)
- `[3, 3, 1, 11, 3]` (triangular)
- `[3, 3, 1, 11, 11]` (triangular)
- `[3, 3, 3, 1, 3]` (triangular)
- `[3, 3, 3, 1, 11]` (triangular)
- `[3, 3, 3, 3, 11]` (triangular)
- `[3, 3, 3, 9, 3]` (triangular)
- `[3, 3, 3, 9, 11]` (triangular)
- `[3, 3, 3, 11, 3]` (triangular)
- `[3, 3, 3, 11, 9]` (triangular)
- `[3, 3, 3, 11, 11]` (triangular)
- `[3, 3, 9, 1, 11]` (triangular)
- `[3, 3, 9, 3, 3]` (triangular)
- `[3, 3, 9, 3, 11]` (triangular)
- `[3, 3, 9, 9, 11]` (triangular)
- `[3, 3, 9, 11, 3]` (triangular)
- `[3, 3, 9, 11, 11]` (triangular)
- `[3, 3, 11, 1, 3]` (triangular)
- `[3, 3, 11, 1, 11]` (triangular)
- `[3, 3, 11, 3, 3]` (triangular)
- `[3, 3, 11, 3, 9]` (triangular)
- `[3, 3, 11, 3, 11]` (triangular)
- `[3, 3, 11, 9, 3]` (triangular)
- `[3, 3, 11, 9, 11]` (triangular)
- `[3, 3, 11, 11, 9]` (triangular)
- `[3, 3, 11, 11, 11]` (triangular)
- `[3, 11, 1, 1, 11]` (triangular)
- `[3, 11, 1, 3, 11]` (triangular)
- `[3, 11, 3, 1, 11]` (triangular)
- `[3, 11, 3, 3, 11]` (triangular)
- `[11, 3, 11, 3, 3]` (triangular)
- `[11, 11, 9, 9, 9]` (triangular)
- `[11, 11, 9, 9, 11]` (triangular)
- `[11, 11, 9, 11, 9]` (triangular)
- `[11, 11, 9, 11, 11]` (triangular)
- `[11, 11, 11, 9, 9]` (triangular)
- `[11, 11, 11, 9, 11]` (triangular)
- `[11, 11, 11, 11, 9]` (triangular)
- `[11, 11, 11, 11, 11]` (triangular)
