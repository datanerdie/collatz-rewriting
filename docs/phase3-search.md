# Phase 3: the search

This note says what is searched for, why a positive answer would mean what it is claimed to
mean, and how to read the results. The results themselves are generated into
`results/phase3/summary.md`.

## 1. What a run is

A *problem* is a rewriting system in one of two search forms. A *run* gives one problem to the
prover published with the paper, with a fixed interpretation type (natural or arctic), a
matrix dimension and a number of values each coefficient may take, under a time limit. A run
ends in one of three ways.

| Outcome | Meaning | How far it can be trusted |
|---|---|---|
| Proved | An interpretation was found for every step | The certificate is verified by `checker/check.py`, which shares no code with the prover |
| Ruled out | The SAT solver reports that no interpretation of that type and size exists | Solver verdict only; not independently certified |
| Timed out | The time limit was reached | Says nothing either way |

For each problem the configurations are tried smallest first and the search stops at the first
proof.

## 2. The two search forms

Let X be a system whose rules all have the three shapes of Phase 1 (dynamic `u▷ → v▷`,
left-end, inner).

- **Left form.** The left-end rules are strict and may be applied only at the left end of the
  string; all other rules are weak.
- **Right form.** The dynamic rules are strict and may be applied only at the right end; all
  other rules are weak. The problem file is written with every string reversed, because the
  prover and the checker treat the left end as the special one.

**Lemma G.** Suppose X without its left-end rules terminates and X without its dynamic rules
terminates. If the left form or the right form of X is solved, then X terminates.

*Proof.* Suppose X does not terminate. By Phase 1, Lemma C, it has an infinite rewrite sequence
from a canonical string. That sequence uses left-end rules infinitely often, because X without
them terminates, and each use is at the left end, because a canonical string has its left
marker only there. So the left form is not solved. The same argument with dynamic rules and
the right end shows the right form is not solved. ∎

The two hypotheses hold for every system used here. For T, S, S2 and the block systems they
were checked in Phases 0 to 2; for the context systems below they are checked by
`harness/phase3.py --validate`; and they pass to any system obtained by deleting rules.

## 3. Residue-class statements

Section 4.5 of the paper asks, for a residue class c modulo 4 or 8: must every non-convergent
Collatz trajectory contain a number congruent to c? It proves this for every class modulo 4
and for the classes 2, 3, 4 and 6 modulo 8, and leaves 1, 5 and 7 modulo 8 open, along with
the weaker statement "5 or 7".

The device is to split the growing step of the map into one rule per residue class and delete
the rule for the class in question. If what remains terminates, a trajectory that avoids the
class cannot go on for ever.

Four encodings are used for each statement modulo 2^b (b = 2 or 3).

| Encoding | Growing step | Source |
|---|---|---|
| `T.c2`, `T.c3` | odd step of T, one rule per odd class, single steps | the paper's T^(Odd/4) and T^(Odd/8) |
| `S.c2`, `S.c3` | even step of the shifted map U, one rule per even class of m = n + 1, single steps | new |
| `T.k2`, `T.k3` | block rules of Phase 2: b steps of T at once | new |
| `S.k2`, `S.k3` | block rules of Phase 2: b steps of U at once | new |

For the first of these, the problems generated here are identical to the files published with
the paper (checked for five of them).

**Lemma H.** Let X be one of these systems and X′ the system X without its dynamic rules for
the classes in a set C. If X′ terminates, then every non-convergent Collatz trajectory
n₀, n₁, n₂, … contains a number in one of the classes of C. For a block system with block
size k, more is true: some n with index a multiple of k is in one of those classes.

*Proof.* Suppose a non-convergent trajectory avoids C (for a block system: avoids C at every
index that is a multiple of k). Every number on it is at least 64, because all smaller numbers
converge. Start from the binary numeral of n₀ (of n₀ + 1 in a shifted system). A dynamic rule
of X′ applies to it: the numeral has enough digits, and the rules of X′ cover every residue
class outside C (checked by `--validate` for every system). By the arithmetic of the rules the
result has the value of the next number on the trajectory (the k-th next for a block system),
and by Phase 1, Lemma E, auxiliary rules bring it back to a binary numeral. Repeating this
gives an infinite rewrite sequence of X′. ∎

Only this direction is needed: a termination proof for X′ proves the statement. For the block
systems the statement proved is stronger than the paper's, so it could in principle be harder;
both follow from the Collatz conjecture.

## 4. The groups of problems

| Group | Problems | What a proof would mean |
|---|---|---|
| Control | The classes 1 and 3 modulo 4, and 3, "1 or 5", "1 or 7" modulo 8, in four encodings and two forms | Nothing new: the paper proved these. A search that fails here is too weak, and an encoding that needs larger matrices than the paper's is a worse encoding |
| Target | The classes 1, 5, 7 and "5 or 7" modulo 8, in four encodings and two forms | A statement the paper leaves open |
| Full | T, S, S2, the context systems and the block systems for k = 2 to 6, in two forms | The Collatz conjecture |
| Negative | The 3n − 1 and 5n + 1 siblings, single-step and in blocks of 2, 3 and 4, in two forms | A bug: each of these systems has an explicit loop |

In the negative group a *partial* result is legitimate. A looping system can still have rules
that are used only finitely often, and the prover may remove those. Only a complete proof would
be wrong.

Any complete proof in the target or full groups is to be treated as a bug until it has been
re-checked by hand and by a second prover.

## 5. The grid

Natural interpretations with 2, 3, 4, 6, 8 or 11 coefficient values and arctic interpretations
with 3, 4, 6 or 8, in dimensions 1 to 3, ordered roughly by the size of the search space. The
time limits used are recorded with each run in `results/phase3/runs.jsonl` and stated in the
summary.

This grid is small. The paper's authors searched up to dimension 7 on 96-core machines without
proving the open statements in their own encoding, so for the encoding `T.c3` nothing new can
be expected here. What this search can show is whether the new encodings behave differently
from the paper's at the sizes where the paper's encoding is already known to fail or succeed.

## 6. What the search found

The tables are in `results/phase3/summary.md`. This section says how to read them.

### 6.1 How far the search reached

Every problem was given 30 configurations, 130 problems in all: 3,731 prover runs and about
17 hours of solver time on four cores. Controls and targets had 120 seconds per run, the full
and negative groups 60 seconds. 17 runs ended in a proof, 3,155 in "ruled out" and 559 in a
timeout.

| Configurations | Outcome |
|---|---|
| Dimension 1 and 2, every type and coefficient range | Decided in every run but three (arctic, dimension 2, 8 values) |
| Dimension 3, natural with 2, 3 or 4 values; arctic with 3 values | Decided in all but three runs |
| Dimension 3, natural with 6 values; arctic with 4 values | Partly decided |
| Dimension 3, natural with 8 or 11 values; arctic with 6 or 8 values | Almost always timed out |

So "no proof" below means: no interpretation exists in dimensions 1 and 2 within these
coefficient ranges, or in dimension 3 with small coefficients, as far as the solver can be
trusted; and nothing is known beyond that. The paper's search went to dimension 7.

### 6.2 Controls: the harness finds what is known to be there

All five statements the paper proved were proved again here, both in the paper's encoding and
in the shifted one, and every proof was accepted by the independent checker.

| Statement | Paper's encoding (`T.c`) | Shifted encoding (`S.c`) |
|---|---|---|
| Visits 1 mod 4 | natural, dimension 2, 4 values | natural, dimension 2, 4 values |
| Visits 3 mod 4 | natural, dimension 2, 4 values | arctic, dimension 2, 6 values |
| Visits 3 mod 8 | arctic, dimension 3, 6 values | natural, dimension 3, 11 values |
| Visits 1 or 5 mod 8 | natural, dimension 2, 4 values | natural, dimension 2, 4 values |
| Visits 1 or 7 mod 8 | arctic, dimension 2, 6 values | arctic, dimension 3, 6 values |

Each cell is the smallest successful configuration over the two search forms.

- **The shifted encoding is never better and sometimes worse.** It succeeds at the same
  configuration in two cases and only at a later one in the search order (a larger dimension
  or coefficient range) in three. Moving the "+1" into an increment
  symbol does not make these statements easier for matrix interpretations; it adds four rules
  that the interpretation must also respect.
- **The block encodings prove only "visits 3 mod 4"**, and that one in dimension 1. The reason
  is elementary: without the block for 3 mod 4, the three remaining blocks of size 2 all shrink
  (n/4, (3n + 1)/4, (3n + 2)/4), so a weight function is enough. For the other four statements
  no block proof was found. This is not a like-for-like failure: by Lemma H a block system
  states that the class is visited at a step count divisible by the block size, which is a
  stronger statement than the paper's.

### 6.3 Targets: nothing new

No proof was found for "visits 1 mod 8", "5 mod 8", "7 mod 8" or "5 or 7 mod 8" in any of the
four encodings or either search form. The only partial results are in the shifted encoding
`S.c3`. Each removes one rule and leaves three or four: `◁s → ◁f` in the left form when class
7 is among those deleted, and `ft▷ → t▷` in the right form when class 5 is. They show that
this one rule is used only finitely often in that system; they do not prove the statements.

For the paper's encoding this was certain in advance, since the authors searched much further.
For the shifted and block encodings it is a new, small negative result: they do not make the
open statements provable at the sizes where the proved statements are provable.

### 6.4 The conjecture itself: no rule can be removed

For none of the 17 encodings of the full problem (T, S, S2, the context systems, and blocks of
2 to 6 steps, shifted or not) did any decided configuration remove even one strict rule. In
particular block acceleration, which was the main new idea, shows no effect. By Phase 2 a
block system admits every interpretation the single-step system admits and possibly more; the
search found none for any block size.

### 6.5 Negative controls: correct, but they do not separate the problems

No looping system was reported as terminating, and no certificate was rejected by the checker.

The outcome for the 3n − 1 and 5n + 1 systems is the same as for the Collatz systems: ruled
out in the small configurations and timed out in the large ones, with no rule removed. At the sizes reached,
this method sees no difference between the Collatz map and maps for which the corresponding
statement is false. That is what one would expect from a search that has found nothing, and it
means the search gives no evidence about the conjecture in either direction.

### 6.6 Trust

- Every proof reported was verified by `checker/check.py`.
- "Ruled out" verdicts are not certified. A sample of 303 of them, one in ten, was repeated
  with a second SAT solver, which agreed on all 303; see `results/phase3/crosscheck.md`. Both solvers are given the same formula by the same
  prover code, so this guards against a solver bug, not against an encoding bug. The check on
  the encoding is the control group.
- All solving used the CaDiCaL build inside the python-sat package through a Python stand-in
  for the command line, with one core per run. It is slower than a native solver, and the
  time limits were short.

### 6.7 Not done

- Dimension 4 and above, and arctic interpretations with entries below zero.
- The second search engine proposed in the original plan (a numerical relaxation to guess
  interpretations for the SAT solver to confirm). It was not attempted.
- A block form of the residue statements that proves exactly the paper's statement and not a
  stronger one. That would need the deleted blocks to be those in which the class occurs at
  any step of the block, which depends on more than k binary digits.
- Certified "ruled out" verdicts (solver proofs checked by a proof checker).
