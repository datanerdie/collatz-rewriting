# Phase 2: block acceleration

This note defines the block-accelerated systems **T.k** and **S.k**, proves that each
terminates on every string if and only if the Collatz conjecture is true, and records what
acceleration does to the siblings used as negative controls.

As in Phase 1, nothing here makes the conjecture easier. The point of acceleration is that an
interpretation has to decrease only across a whole block of k steps, not at every single step,
which enlarges the set of interpretations that would count as a proof. Whether that helps is
measured in Phase 3.

Notation and symbols are those of `docs/phase1-shifted-system.md`.

## 1. Blocks

Let T be the Collatz map n → n/2 or (3n + 1)/2, and U the shifted map m → 3m/2 or (m + 1)/2.

**Lemma F (blocks).** Fix k ≥ 1 and 0 ≤ r < 2^k. There is a number j, depending only on r, with

    T^k(2^k·x + r) = 3^j·x + c     for every x ≥ 0,   where 0 ≤ c < 3^j
    U^k(2^k·x + r) = 3^j′·x + c′   for every x ≥ 0,   where 0 ≤ c′ ≤ 3^j′

Here j is the number of odd steps among the k steps of T, and j′ the number of even steps among
the k steps of U.

*Proof.* Follow the numbers A·x + B through the k steps, starting from A = 2^k, B = r. Before
step i the coefficient A is 2^(k−i) times a power of 3, so it is even and the parity of A·x + B
is the parity of B for every x: all these numbers take the same branch. A halving branch halves
A; a growing branch multiplies it by 3/2. For T, the bound B ≤ A − 1 is preserved: B/2 ≤ A/2 − 1/2
on an even step, and (3B + 1)/2 ≤ (3A − 2)/2 on an odd one. For U, the bound B ≤ A is
preserved: 3B/2 ≤ 3A/2 on an even step; on an odd step B is odd and A is even, so B ≤ A − 1 and
(B + 1)/2 ≤ A/2. ∎

So k steps of T turn the last k binary digits into exactly j ternary digits, the base-3 numeral
of c. For U the same holds when c′ < 3^j′; when c′ = 3^j′ the result is 3^j′·(x + 1), an
increment followed by j′ zeros.

`harness/phase2.py` computes every block rule this way and re-verifies each one as an exact
identity of affine functions.

## 2. The accelerated systems

For a block size k ≥ 2:

- **T.k** is the paper's system T with its two dynamic rules replaced by the 2^k rules
  `w▷ → τ▷`, one for each string w of k binary digits, where τ is the ternary numeral given by
  Lemma F. It has 2^k + 9 rules.
- **S.k** is the shifted system S with its three dynamic rules replaced by the 2^k rules
  `w▷ → τ▷` or `w▷ → s0…0▷` given by Lemma F for U. It has 2^k + 12 rules.

For k = 2:

| System | Block rules |
|---|---|
| T.k2 | `ff▷ → ▷`, `ft▷ → 1▷`, `tf▷ → 2▷`, `tt▷ → 22▷` |
| S.k2 | `ff▷ → 00▷`, `ft▷ → s▷`, `tf▷ → 2▷`, `tt▷ → s0▷` |

No rule applies once fewer than k binary digits remain before `▷`. An accelerated system
therefore does not stop at one particular value: it stops at every value below 2^k. In
particular S.k needs neither the two-digit context of S nor the second left marker of S2.

**Theorem 3.** Let k ≥ 2 be such that every positive integer below 2^k reaches 1 under T (true
for k ≤ 6 by direct computation, which is all that is used here). Then each of T.k and S.k
terminates on every string if and only if the Collatz conjecture is true.

*Proof for T.k.* The argument is that of Theorem 3.17 of the paper, as rewritten for S in
Phase 1, with these ingredients.

- *Arithmetic.* Auxiliary rules do not change the value of a canonical string; a block rule
  replaces a value n by T^k(n) (Lemma F).
- *Two terminating subsystems.* Without its block rules, T.k is T without its dynamic rules,
  which terminates (Lemma 3.15 of the paper, checked in Phase 0). Without its left-end rules it
  terminates by the interpretation `f`, `t`: 2x + 1; `0`, `1`, `2`: 2x; `▷`: x on the reversed
  system: a block of k binary digits has interpretation 2^k·x + 2^k − 1, and at most k ternary
  digits have 2^j·x with j ≤ k. Certificates `T.kN-without-left-end-rules-reversed`.
- *Canonical strings suffice.* Every rule has one of the three shapes of Phase 1, Lemma C.
- *Stopping.* If a block rule applies to a canonical string, the string ends in k binary
  digits after a prefix of value x ≥ 1, so its value is at least 2^k.
- *Progress.* A canonical string of value at least 2^k rewrites by auxiliary rules to the
  binary numeral of that value (Phase 1, Lemma E), which has at least k digits after its
  marker, so a block rule applies.

Suppose T.k has an infinite rewrite sequence. It has one from a canonical string of some value
n₀, and it uses block rules infinitely often, so T^(ki)(n₀) ≥ 2^k for every i. If the conjecture
were true, the trajectory of n₀ would eventually stay in {1, 2}, and 2 < 2^k. So the conjecture
is false.

Conversely, suppose the trajectory of n₀ never reaches 1. Then no iterate is below 2^k, because
every number below 2^k does reach 1. By progress, the binary numeral of n₀ rewrites to a string
of value T^k(n₀), that one to a string of value T^(2k)(n₀), and so on for ever. ∎

*Proof for S.k.* The same, with U in place of T. The subsystem without left-end rules uses the
interpretation of Phase 1, Lemma B (`s`: 2x); a block rule that produces an increment has j′ ≤
k − 1 ternary digits after it, so the right side is at most 2^k·x. If the conjecture is true,
every U-trajectory eventually stays in {2, 3}, below 2^k. If the U-trajectory of m₀ never
reaches 2, no iterate m is below 2^k, because m − 1 < 2^k would reach 1 under T. ∎

**Corollary.** For T.k and S.k, as in Phase 1: the conjecture is true if and only if the
left-end rules can be used only finitely often when applied at the left end of the string.
The files `problems/phase2/*.srs` state each accelerated system in this form.

## 3. Acceleration can only help the search

**Proposition.** Every block rule of T.k is a rewrite sequence of T. Every block rule of S.k is
a rewrite sequence of the single-step rules `f▷ → 0▷`, `t▷ → s▷`, the carry and increment
rules, and the three value-preserving rules `0s → 1`, `1s → 2`, `2s → s0`.

*Proof.* Checked by search for every block rule and every k from 2 to 6. For example
`tt▷ → t2▷ → 2t▷ → 22▷` in T, and `tf▷ → t0▷ → 1t▷ → 1s▷ → 2▷` for S. The three extra rules are
needed only because block rules write their result as a plain ternary numeral. ∎

Two consequences:

- An accelerated system has no rewrite sequences that the single-step system lacks, so it
  terminates whenever the single-step system does.
- Any interpretation that weakly decreases on every single-step rule also weakly decreases on
  every block rule, and strictly if it is strict on the single steps inside the block. So every
  interpretation proof for the single-step system is also one for the accelerated system. The
  converse is false, which is the reason to try acceleration at all.

The price is the number of rules, which doubles with each unit of k, and with it the number of
constraints a solver must satisfy.

## 4. What acceleration does to the negative controls

The siblings T⁻, S⁻ (3n − 1) and T5 (5n + 1) loop because their maps have extra cycles. An
accelerated sibling looks at the trajectory only every k steps and stops at any value below
2^k, so a cycle survives acceleration only if the values it shows at those times are all at
least 2^k.

| Sibling | k = 2 | k = 3 | k = 4 | k = 5 | k = 6 |
|---|---|---|---|---|---|
| T⁻ (3n − 1) | loops from 5 | loops from 10 | loops from 17 | no loop from the known cycles | no loop from the known cycles |
| S⁻ (3n − 1, shifted) | loops from 4 | loops from 9 | loops from 16 | no loop from the known cycles | no loop from the known cycles |
| T5 (5n + 1) | loops from 13 | loops from 13 | loops from 17 | no loop from the known cycles | no loop from the known cycles |

This matters for how Phase 3 is read.

- **For k ≤ 4 the controls work as intended.** Each accelerated sibling has an explicit loop, so
  a search that reports it terminating has a bug.
- **For k = 5 and 6 there is no machine-checkable control among these siblings.** The known
  cycles of 3n − 1 have minimum 5 and 17, both below 32. If 3n − 1 has no further cycles and no
  divergent trajectory, as is conjectured, then its accelerated systems for k ≥ 5 really do
  terminate. A method that proved T.k5 and also "proved" T⁻.k5 would not have been caught
  proving something false.
- **5n + 1 is believed to have divergent trajectories**, which would make its accelerated
  systems non-terminating for every k, but there is no finite witness to check a prover
  against.

So the rule "a method that works equally well for 3n − 1 must be wrong" applies to the
single-step systems and to block sizes up to 4. For larger blocks it has to be replaced by the
other controls: the independent checker, and agreement with the single-step systems on the
variants that are known to be provable.

## 5. Blocks and the residue sieve

A block of k binary digits is a residue class modulo 2^k, so the block rules are the forward
sieve of the original discussion written as rewrite rules. A block *shrinks* if 3^j < 2^k.

| k | 2 | 3 | 4 | 5 | 6 | 16 |
|---|---|---|---|---|---|---|
| Shrinking blocks | 3 of 4 | 4 of 8 | 11 of 16 | 26 of 32 | 42 of 64 | 58,651 of 65,536 (89.49%) |

The counts are the same for T and for U. The last column confirms the figure of 89.5% quoted in
the discussion this work started from. The four residue classes modulo 32 that never fall below
their start within five steps are 7, 15, 27 and 31, also as quoted there. These two counts
measure different things: a block that does not shrink after exactly k steps may still have
dipped below its start earlier.

## 6. Relation to the paper

Section 4.5 of the paper also uses dynamic rules that read the last two or three binary
digits, to ask which residue classes modulo 4 and 8 a non-convergent trajectory must visit.
Those rules still apply one step of the map at a time and keep the digits they did not consume;
the block rules here apply k steps and consume all k digits.

## 7. Limits

- Theorem 3 is a written proof built on the Phase 1 lemmas; it has not been machine-checked.
- The simulation in `results/phase2/summary.md` covers every rewrite sequence from the listed
  start strings and block sizes 2 to 6. It would have exposed a wrong block rule; it cannot
  establish termination in general.
