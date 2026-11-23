# Dimension 1: an impossibility theorem

Phase 3 reported that a SAT solver found no one-dimensional interpretation with coefficients
below a fixed bound. This note replaces that by a proof with no bound on the coefficients and
no bound on the block size.

The paper raises the question itself. Its closing section says that there may be no matrix
interpretation at all that proves termination of its system T, and that this "would be an
interesting result in itself". The paper proves such a statement for an older unary system of
Zantema, not for T. What follows settles the smallest case for T, dimension 1, and nothing
beyond it.

## 1. Statement

Notation is that of `docs/phase1-shifted-system.md` and `docs/phase2-block-acceleration.md`.
T.k is the paper's system with its dynamic rules replaced by the 2^k block rules for k steps;
T.1 is T itself. A *one-dimensional natural interpretation* gives every symbol x a function

    [x](n) = p_x·n + q_x      with integers p_x ≥ 0 and q_x ≥ 0,

and a string the composition of the functions of its symbols.

**Theorem 4.** Let k ≥ 1. There is no one-dimensional natural interpretation, with
coefficients of any size, that solves any part of either search form of T.k. That is:

- *(left form)* none under which every rule of T.k is weakly decreasing and some left-end rule
  is strictly decreasing, with the leftmost symbol as the outermost function;
- *(right form)* none under which every rule is weakly decreasing and some block rule is
  strictly decreasing, with the rightmost symbol as the outermost function.

"Weakly decreasing" for a rule ℓ → r means [ℓ](n) ≥ [r](n) for every n ≥ 0, and "strictly"
means [ℓ](n) > [r](n) for every n ≥ 0. For functions p·n + q these hold exactly when p ≥ p′ and
q ≥ q′ (respectively q > q′), which is the test the checker applies. So in dimension 1 nothing
is lost by comparing coefficients, and the theorem is about all such functions.

**In plain terms.** No rule "each symbol multiplies by something and adds something" can
serve as a measure that never increases and sometimes drops, whatever the multipliers and
however many steps are grouped into a block.

## 2. What is used

Write a, b for the multipliers p_f, p_t of the binary digits and c₀, c₁, c₂ for those of the
ternary digits 0, 1, 2. Only these rules of T.k are used:

| Rules | Where |
|---|---|
| The six carry rules `f0 → 0f`, `f1 → 0t`, `f2 → 1f`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t` | both forms |
| The three left-end rules `◁0 → ◁t`, `◁1 → ◁ff`, `◁2 → ◁ft` | left form; only `◁2 → ◁ft` in the right form |
| The block rule for all-odd steps, `t…t▷ → 2…2▷` (k digits on each side) | both forms |
| The block rule for all-even steps, `f…f▷ → ▷` | right form |
| The fact that a block rule other than `f…f▷ → ▷` writes at least one non-zero ternary digit | right form |

The two block rules come from T^k(2^k·x + 2^k − 1) = 3^k·x + 3^k − 1 and T^k(2^k·x) = x. For
the last line: a block with residue r ≠ 0 writes the numeral of T^k(r), and T maps positive
numbers to positive numbers.

For a string of m equal digits the constant part of its function is q·(1 + p + … + p^(m−1));
write Σ_p for 1 + p + … + p^(k−1).

## 3. Proof for the left form

The functions compose with the leftmost symbol outermost. If p_◁ = 0, both sides of every
left-end rule are the constant q_◁, so none is strict. Assume p_◁ ≥ 1. Dividing by p_◁, the
left-end rules give

    (L1) c₀ ≥ b          q₀ ≥ q_t
    (L2) c₁ ≥ a²         q₁ ≥ (a + 1)·q_f
    (L3) c₂ ≥ a·b        q₂ ≥ a·q_t + q_f

with a strict inequality between the constants for a strict rule. The carry rules give

    f1 → 0t:   a·c₁ ≥ c₀·b        (C2) a·q₁ + q_f ≥ c₀·q_t + q₀
    f2 → 1f:   a·c₂ ≥ c₁·a        (C3) a·q₂ + q_f ≥ c₁·q_f + q₁
    t0 → 1t:   b·c₀ ≥ c₁·b        (C4) b·q₀ + q_t ≥ c₁·q_t + q₁
    t1 → 2f:   b·c₁ ≥ c₂·a        (C5) b·q₁ + q_t ≥ c₂·q_f + q₂
    t2 → 2t:                      (C6) b·q₂ + q_t ≥ c₂·q_t + q₂

**Case a = 0.** By (C3) and (L2), q_f ≥ c₁·q_f + q₁ ≥ q₁ ≥ q_f, so q₁ = q_f and (L2) is not
strict. From a·c₁ ≥ c₀·b and c₀ ≥ b, b = 0. Then (C5) gives q_t ≥ q₂, (L3) gives q₂ ≥ q_f,
(C2) gives q_f ≥ q₀, and (L1) gives q₀ ≥ q_t. All four are equal, so (L1) and (L3) are not
strict.

**Case a ≥ 1, b = 0.** Then c₂·a ≤ b·c₁ = 0 gives c₂ = 0, a·c₂ ≥ c₁·a gives c₁ = 0, and (L2)
demands c₁ ≥ a² ≥ 1. Impossible.

**Case a ≥ 1, b ≥ 1.** Then c₀ ≥ c₁ and c₂ ≥ c₁, and c₁ ≥ a² ≥ 1, so all five multipliers are
positive. From b·c₁ ≥ c₂·a ≥ c₁·a, b ≥ a. From a·c₁ ≥ c₀·b ≥ c₁·b, a ≥ b. So a = b; call it σ.
Then σ·c₁ ≥ c₀·σ gives c₁ ≥ c₀, so c₀ = c₁; and σ·c₁ ≥ c₂·σ gives c₂ = c₁. Call the common
value τ. By (L2), τ ≥ σ² ≥ σ.

The all-odd block rule `t…t▷ → 2…2▷` gives σ^k·q_▷ + q_t·Σ_σ ≥ τ^k·q_▷ + q₂·Σ_τ. Since τ ≥ σ,
the right side is at least σ^k·q_▷ + q₂·Σ_σ, so q_t ≥ q₂. With (L3):

    q_t ≥ q₂ ≥ σ·q_t + q_f ≥ q_t + q_f.

Hence q_f = 0, q₂ = q_t, and (σ − 1)·q_t = 0.

- If q_t = 0, then q₂ = 0, (C3) gives q₁ = 0 and (C2) gives q₀ = 0. All five constants are
  zero and no left-end rule is strict.
- If q_t > 0, then σ = 1, and (C6) reads 0 ≥ (τ − 1)·q_t, so τ = 1. Now (C3) gives q₂ ≥ q₁,
  (C4) gives q₀ ≥ q₁, and (C2) gives q₁ ≥ q_t + q₀ ≥ q_t + q₁, so q_t = 0. Contradiction. ∎

## 4. Proof for the right form

Here the rightmost symbol is outermost; equivalently every string is reversed, as in the
problem files. If p_▷ = 0 both sides of every block rule are the constant q_▷. Assume p_▷ ≥ 1.
For a block rule w▷ → u▷ write Q(w), Q(u) for the constant parts of the functions of w and u.
The rule is weakly decreasing when the multiplier of w is at least that of u and Q(w) ≥ Q(u),
and strict when also Q(w) > Q(u).

The all-even block gives a^k ≥ 1, so a ≥ 1. The all-odd block gives b ≥ c₂ and

    (B) q_t·Σ_b ≥ q₂·Σ_{c₂}.

The carry rules, with the order of composition reversed, give

    f0 → 0f:                      (R1) c₀·q_f + q₀ ≥ a·q₀ + q_f
    f1 → 0t:   c₁·a ≥ b·c₀        (R2) c₁·q_f + q₁ ≥ b·q₀ + q_t
    f2 → 1f:   c₂ ≥ c₁            (R3) c₂·q_f + q₂ ≥ a·q₁ + q_f
    t0 → 1t:   c₀·b ≥ b·c₁        (R4) c₀·q_t + q₀ ≥ b·q₁ + q_t
    t1 → 2f:   c₁·b ≥ a·c₂        (R5) c₁·q_t + q₁ ≥ a·q₂ + q_f
    t2 → 2t:                      (R6) c₂·q_t + q₂ ≥ b·q₂ + q_t

and the left-end rule `◁2 → ◁ft` gives

    (R7) c₂·q_◁ + q₂ ≥ a·b·q_◁ + b·q_f + q_t.

**Case A: c₁ ≥ 1.** From c₁·b ≥ a·c₂ ≥ a·c₁, b ≥ a ≥ 1. Then c₀ ≥ c₁, and c₁·a ≥ b·c₀ ≥ b·c₁
gives a ≥ b. So a = b = σ. As before c₀ = c₁ = c₂ = τ, and b ≥ c₂ gives σ ≥ τ ≥ 1.

*If σ ≥ 2.* (R6) is (τ − 1)·q_t ≥ (σ − 1)·q₂ and (R7) is q₂ ≥ (σ² − τ)·q_◁ + σ·q_f + q_t, with
σ² − τ > 0. So

    (σ − 1)·q_t ≥ (τ − 1)·q_t ≥ (σ − 1)·q₂ ≥ (σ − 1)·(q_t + σ·q_f + (σ² − τ)·q_◁).

Hence q_f = 0, q₂ = q_t, and (τ − 1)·q_t = (σ − 1)·q_t. If q_t = 0, then q₂ = 0, (R3) gives
q₁ = 0 and (R1) gives q₀ = 0: all constants of digits are zero, every Q is zero, and no block
rule is strict. If q_t > 0, then τ = σ; (R1) gives q₀ = 0; (R2) gives q₁ ≥ q_t; and (R4) gives
σ·q_t ≥ σ·q₁ + q_t, so q₁ < q_t. Contradiction.

*If σ = 1,* then τ = 1. (R4) gives q₀ ≥ q₁, and with (R2), q_f + q₁ ≥ q₀ + q_t ≥ q₁ + q_t, so
q_f ≥ q_t. (R3) gives q₂ ≥ q₁. (R7) gives q₂ ≥ q_f + q_t. (R5) gives q_t + q₁ ≥ q₂ + q_f ≥
q₁ + q_f, so q_t ≥ q_f. So q_f = q_t; call it u. Then (R5) gives q₁ ≥ q₂, so q₁ = q₂; call it
v; and v ≥ 2u by (R7). Now (B) reads k·u ≥ k·v ≥ 2k·u, so u = 0 and v = 0, and (R2) gives
q₀ = 0. Every Q is zero and no block rule is strict.

**Case B: c₁ = 0.** Then a·c₂ ≤ c₁·b = 0 gives c₂ = 0, and b·c₀ ≤ c₁·a = 0. By (R3) and (R5),

    q₂ ≥ a·q₁ + q_f ≥ a²·q₂ + (a + 1)·q_f,

so q_f = 0; and q₂ = q₁ if a = 1, while q₂ = q₁ = 0 if a ≥ 2.

*If b ≥ 1,* (R6) reads q₂ ≥ b·q₂ + q_t, so q_t = 0. With q_f = 0, Q(w) = 0 for every binary
block w, and no block rule is strict.

*If b = 0,* (R6) reads q₂ ≥ q_t and (B) reads q_t ≥ q₂, so q₂ = q_t; call it v. If a ≥ 2 then
v = 0 and again every Q(w) is zero. So let a = 1; then q₁ = v as well. Because q_f = 0, a = 1
and b = 0, Q(w) = v for every block w that contains a `t`, and Q(w) = 0 for the all-even
block, which is therefore not strict. For any other block, read u starting from the outermost
digit. It contains a non-zero digit. If the outermost digit is non-zero, Q(u) = v, because
c₁ = c₂ = 0. Otherwise u begins with i ≥ 1 zeros followed by a non-zero digit, and
Q(u) = q₀·(1 + c₀ + … + c₀^(i−1)) + c₀^i·v. If c₀ ≥ 1 this is at least v. If c₀ = 0 it equals
q₀, and (R4) reads q₀ ≥ q_t = v. In every case Q(u) ≥ v = Q(w), so the rule is not strict. ∎

## 5. What the proofs show beyond the statement

- **The left-end rules and the carries almost fix the interpretation.** In both forms the
  multipliers are forced to be one value σ for both binary digits and one value τ for all three
  ternary digits (or to degenerate to zero). Everything else follows from a single block rule,
  the one for all-odd steps.
- **The obstruction is the all-odd block.** It turns k binary digits into k ternary digits of
  the largest value. Remove it and interpretations exist: this is why "visits 3 mod 4" was
  provable in dimension 1 in Phase 3 (that statement deletes exactly this block for k = 2).
- **Longer blocks do not help in dimension 1.** This is the first rigorous statement in this
  repository about the main idea of Phase 2, and it is negative.

## 6. Machine checks

`harness/dimension1.py` gives the same question to the SMT solver z3 for every problem of
Phase 3, with unbounded integer coefficients. Results are in `results/dimension1/summary.md`.

- **Natural.** The constraints contain products of unknowns, which z3 is not guaranteed to
  decide. Where it answers "none" for T and T.k (k up to 6), it confirms instances of
  Theorem 4. It is also run on the shifted systems, the context systems, the residue-class
  problems and the looping siblings, for which there is no written proof here.
- **Arctic.** A one-dimensional arctic interpretation is x ↦ max(m + x, v) with m and v
  integers or −∞. The constraints are linear, so z3 decides them. Entries below zero are
  allowed, which Phase 3 did not search. There is no written proof for the arctic case; the
  result rests on z3.
- **Positive controls.** For the problems where Phase 3 found a one-dimensional proof or
  partial proof, z3 finds an interpretation too, and the checker accepts it. So the encoding
  given to z3 is not vacuously unsatisfiable.

## 7. Limits

- Theorem 4 is a written proof. It has been checked against z3 for k = 1 to 6 where z3
  answers, not formalised in a proof assistant.
- It covers natural interpretations of dimension 1 only. Dimension 2 is open: Phase 3 ruled it
  out for small coefficients only. Dimension 2 allows genuinely different behaviour (matrices
  do not commute), and the argument above does not carry over.
- It covers the two search forms used in this repository, which are the paper's (relative top
  termination of the left-end rules, or of the dynamic rules on the reversed system). Other
  ways of using interpretations, such as first transforming the system, are not covered.
- It says nothing about the Collatz conjecture. It says that one very small class of proofs
  does not contain one.
- I did not find this statement in the paper, but I have not searched the wider literature
  for it, and it may be known to people who work on termination.
