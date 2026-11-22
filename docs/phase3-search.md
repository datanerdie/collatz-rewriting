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
