# Phase 1: the shifted systems

This note fixes two "shifted" rewriting systems, **S** and **S2**, and proves that each
terminates on every string if and only if the Collatz conjecture is true. It is the analogue,
for the shifted systems, of Theorem 3.17 of Yolcu, Aaronson & Heule (2023), and the proof
follows theirs step by step.

Nothing here makes the conjecture easier. The result only says that S and S2 are *correct*
reformulations, so that a termination proof for either would be a proof of the conjecture.
Whether they are any *easier* for automated search is the question for Phase 3.

## What is proved, and how

| Statement | How it is established |
|---|---|
| Lemma 0: the shifted map is the Collatz map moved by one | Two lines of algebra, below |
| Lemma A: the rules do the arithmetic they claim | Exact identities of affine functions, checked by `harness/phase1.py` |
| Lemma B: S without its left-end rules terminates; S without its dynamic rules terminates | Certificates in `results/phase1/`, verified by `checker/check.py` |
| Lemma C: only strings of the form `◁ digits ▷` matter | Pen-and-paper, below (the paper's Appendix A argument) |
| Lemmas D and E: rewriting stops at the stop value, and only there | Pen-and-paper, below |
| Theorem: S terminates ⇔ Collatz | Pen-and-paper, from the lemmas |
| All of the above, on instances | Exhaustive simulation, `results/phase1/summary.md` |

The pen-and-paper parts have not been formalised in a proof assistant.

## 1. The shifted map

The Collatz map in its usual shortened form is

    T(n) = n/2          if n is even
    T(n) = (3n + 1)/2   if n is odd

on the positive integers; the conjecture says every trajectory reaches 1, after which it
cycles 1 → 2 → 1. Put m = n + 1 and define, on the integers m ≥ 2,

    U(m) = 3m/2         if m is even
    U(m) = (m + 1)/2    if m is odd

**Lemma 0.** U(n + 1) = T(n) + 1 for every n ≥ 1. Hence the T-trajectory of n reaches 1 if and
only if the U-trajectory of n + 1 reaches 2, if and only if it reaches 3.

*Proof.* If n is even then n + 1 is odd and U(n + 1) = (n + 2)/2 = n/2 + 1. If n is odd then
n + 1 is even and U(n + 1) = 3(n + 1)/2 = (3n + 1)/2 + 1. The cycle 1 → 2 → 1 of T becomes the
cycle 2 → 3 → 2 of U. ∎

In the shifted picture the growing step is multiplication by 3/2 with nothing added, and all of
the "+1" has moved into the halving step, which rounds up.

## 2. Symbols and values

Each symbol is a function, and a string is the composition of its symbols applied from left to
right.

| Symbol | Function | Role |
|---|---|---|
| `f` | x → 2x | binary digit 0 |
| `t` | x → 2x + 1 | binary digit 1 |
| `0`, `1`, `2` | x → 3x, 3x + 1, 3x + 2 | ternary digits |
| `s` | x → x + 1 | increment |
| `◁` | the constant 1 | left end marker (S) |
| `◁₂`, `◁₃` | the constants 2 and 3 | left end markers (S2) |
| `▷` | x → x | right end marker |

A *digit* is one of `f t 0 1 2 s`. A *canonical string* is a left marker, then any digits, then
`▷`; its *value* is the number obtained by applying the digits in order to the marker's
constant. For example `◁ft▷` has value 2·(2·1) + 1 = 5, the binary numeral 101. A canonical
string whose digits are all binary is the ordinary binary numeral of its value.

Every digit maps an integer x ≥ 1 to an integer greater than x. So a canonical string with k
digits has value at least k plus the marker's constant, and the only canonical string of S with
value 1 is `◁▷`.

## 3. The system S

S has 15 rules over 8 symbols.

| Group | Rules | Meaning |
|---|---|---|
| Dynamic, D | `f▷ → 0▷` | 2x → 3x |
| | `ft▷ → t▷` | 4x + 1 → 2x + 1 |
| | `tt▷ → sf▷` | 4x + 3 → 2x + 2 = 2(x + 1) |
| Carry | `f0 → 0f`, `f1 → 0t`, `f2 → 1f`, `t0 → 1t`, `t1 → 2f`, `t2 → 2t` | move a ternary digit left |
| Increment | `fs → t`, `ts → sf` | move an increment left |
| Left end, B | `◁0 → ◁t`, `◁1 → ◁ff`, `◁2 → ◁ft`, `◁s → ◁f` | absorb a digit into the marker |

The carry and left-end rules for ternary digits are exactly those of the paper's system T. The
*auxiliary* rules are all rules other than the dynamic ones.

The even step is the bare relabelling `f▷ → 0▷`. The odd step reads two digits so that it
cannot fire on `◁t▷`, the string for 3, which is where the system is meant to stop.

**Theorem 1.** S terminates on every string if and only if the Collatz conjecture is true.

### Lemma A (arithmetic)

For every auxiliary rule ℓ → r, the two sides are the same function. For every dynamic rule
u▷ → v▷, the function of v equals U applied to the function of u, at every integer x ≥ 1.

*Proof.* Direct computation; for instance `ts → sf` is (2x + 1) + 1 = 2(x + 1), and
`tt▷ → sf▷` is U(4x + 3) = (4x + 4)/2 = 2(x + 1). `harness/phase1.py` verifies all 15 rules as
exact identities between affine functions. ∎

*Consequence.* If N is canonical and N → N′ by an auxiliary rule, then N′ is canonical with the
same value. If N → N′ by a dynamic rule, then N′ is canonical with value U(value of N).

### Lemma B (two terminating subsystems)

S without its left-end rules terminates, and S without its dynamic rules terminates.

*Proof.* Interpret each symbol as a function on the natural numbers and a string by applying
its symbols from left to right. Every rule strictly decreases the result, for every argument:

| Subsystem | `f`, `t` | `0`, `1`, `2` | `s` | `◁` | `▷` |
|---|---|---|---|---|---|
| without left-end rules | 2x + 1 | 2x | 2x | — | x |
| without dynamic rules | x + 1 | 4x | 2x + 1 | x + 1 | — |

These are the interpretations of the paper's Lemma 3.15 with a value added for `s`. The
certificates `S-without-left-end-rules-reversed` and `S-without-dynamic-rules-reversed` are
accepted by `checker/check.py`. ∎

### Lemma C (canonical strings suffice)

If S terminates on every canonical string, then S terminates on every string.

*Proof.* Every rule of S has one of three shapes: `u▷ → v▷`, `◁u → ◁v`, or `u → v`, with u and
v strings of digits (checked by `harness/phase1.py`). So no rule creates, deletes or moves an
end marker, and no rule reads across one.

Suppose a string X has an infinite rewrite sequence. Then so does any string containing X; put
an end marker at each end of X and cut the result at its end markers into blocks c N d, where c
and d are end markers and N is a string of digits. Each rewrite step changes the digits of
exactly one block and leaves all markers in place. There are finitely many blocks, so one
block c N d is rewritten infinitely often.

- If d is not `▷`, no dynamic rule ever applies to this block, so it is rewritten by S without
  its dynamic rules, which terminates by Lemma B.
- If c is not `◁`, no left-end rule ever applies to it, so it is rewritten by S without its
  left-end rules, which terminates by Lemma B.

Hence c = `◁` and d = `▷`: the block is a canonical string with an infinite rewrite
sequence. ∎

### Lemma D (stopping)

No dynamic rule applies to a canonical string of value 3, nor to any string it rewrites to.
No rule at all applies to `◁▷`, the only canonical string of value 1.

*Proof.* A dynamic rule needs the string to end in `f▷`, `ft▷` or `tt▷`. Writing x ≥ 1 for the
value of what precedes, the string's value is then 2x (even), 4x + 1 ≥ 5, or 4x + 3 ≥ 7; never
3. Auxiliary steps keep the value at 3 by Lemma A, so the same holds afterwards. ∎

### Lemma E (progress)

Let N be a canonical string whose value m is at least 2 and not 3. Then some sequence of
auxiliary steps followed by one dynamic step leads from N to a string of value U(m).

*Proof.* Apply auxiliary rules to N for as long as any applies. This stops, by Lemma B; call
the result N′. It has value m by Lemma A.

N′ has no digit among `0 1 2 s`. Otherwise take the leftmost such digit: the symbol to its left
is `◁`, `f` or `t`, and each of the twelve possible pairs is the left side of an auxiliary
rule, contradicting the choice of N′.

So N′ is the binary numeral of m. It has at least one digit because m ≥ 2. If it ends in `f`,
the rule `f▷ → 0▷` applies. If it ends in `t`, it has at least two digits because m ≠ 3, so it
ends in `ft` or `tt` and the corresponding dynamic rule applies. By Lemma A the result has
value U(m). ∎

### Proof of Theorem 1

*If the conjecture is true, S terminates.* Suppose S has an infinite rewrite sequence. By
Lemma C it has one that starts from a canonical string N₀, and N₀ is not `◁▷`, so its value m₀
is at least 2. The sequence uses dynamic rules infinitely often, because S without them
terminates (Lemma B). By Lemma A the value just before the k-th dynamic step is
U applied k − 1 times to m₀, and by Lemma D that value is never 3. So the U-trajectory of m₀
never reaches 3, and by Lemma 0 the T-trajectory of m₀ − 1 never reaches 1. The conjecture is
false.

*If S terminates, the conjecture is true.* Suppose the T-trajectory of some n₀ never reaches 1.
Then it never reaches 2 either, so by Lemma 0 the U-trajectory m₀, m₁, m₂, … of m₀ = n₀ + 1
consists of numbers that are at least 2 and never 3. Let N₀ be the binary numeral of m₀. Lemma E
gives a string N₁ of value m₁ with N₀ →⁺ N₁, then N₂ of value m₂ with N₁ →⁺ N₂, and so on: an
infinite rewrite sequence. ∎

### Corollary (the form used for search)

Write B for the four left-end rules. The Collatz conjecture is true if and only if the rules of
B can be used only finitely often in any rewrite sequence of S in which they are applied at the
left end of the string. In the paper's notation: SN(B_top / S).

*Proof.* If S terminates the statement is immediate. Conversely, if S does not terminate, then
by Lemma C there is an infinite sequence from a canonical string; it uses B infinitely often
because S without B terminates (Lemma B); and in a canonical string `◁` occurs only at the left
end, so every use of B is at the left end. ∎

This is the analogue of the paper's Lemma 3.18. It matters because left-end ("top") termination
may be proved with a weaker kind of interpretation, which enlarges the search space.

## 4. The system S2

S2 has 18 rules over 9 symbols. It uses two left markers, `◁₂` and `◁₃`, standing for the
leading binary digits 10 and 11, so that the numbers 2 and 3 are the bare strings `◁₂▷` and
`◁₃▷`. Then neither dynamic rule needs a context.

| Group | Rules |
|---|---|
| Dynamic | `f▷ → 0▷`, `t▷ → s▷` |
| Carry | as in S |
| Increment | as in S |
| Left end | `◁₂0 → ◁₃f`, `◁₂1 → ◁₃t`, `◁₂2 → ◁₂ff`, `◁₃0 → ◁₂ft`, `◁₃1 → ◁₂tf`, `◁₃2 → ◁₂tt`, `◁₂s → ◁₃`, `◁₃s → ◁₂f` |

**Theorem 2.** S2 terminates on every string if and only if the Collatz conjecture is true.

*Proof.* As for Theorem 1, with these changes.

- Lemma A: all 18 rules are verified by `harness/phase1.py`. The left-end rules are the
  identities 6 = 3·2, 7 = 2·3 + 1, 8 = 2·2·2, 9 = 2·(2·2) + 1, 10 = 2·(2·2 + 1),
  11 = 2·(2·2 + 1) + 1, 3 = 2 + 1 and 4 = 2·2.
- Lemma B: the same interpretations, with x + 1 for both markers; certificates
  `S2-without-left-end-rules-reversed` and `S2-without-dynamic-rules-reversed`.
- Lemma C: unchanged; a left-end rule may swap one left marker for the other, which does not
  affect the argument.
- Lemma D: every canonical string has value at least 2, and a dynamic rule needs the string to
  end in `f▷` or `t▷`, giving value 2x ≥ 4 or 2x + 1 ≥ 5. So no dynamic rule applies at value
  2 or 3.
- Lemma E: for a canonical string of value other than 2 and 3, the leftmost digit among
  `0 1 2 s` has a left marker, `f` or `t` on its left, and all sixteen pairs are left sides of
  auxiliary rules. The binary numeral that results has at least one digit after its marker, so
  a dynamic rule applies.
- The trajectory statement becomes "never reaches 2 or 3", which by Lemma 0 is "the
  T-trajectory never reaches 1 or 2", and that is the failure of the conjecture. ∎

The corollary holds for S2 with its eight left-end rules.

## 5. Siblings with extra cycles

These systems simulate maps that are known to have more than one cycle. They do not terminate,
and `harness/phase1.py` exhibits an explicit looping rewrite sequence for each. They are the
negative controls for Phase 3: no search may ever report one of them as terminating.

| System | Map | Rules | Loop through |
|---|---|---|---|
| T⁻ | n → n/2 or (3n − 1)/2 | T with `t▷ → 2▷` replaced by `t▷ → 1▷` | 5 and 17 |
| S⁻ | m → 3m/2 or (m − 1)/2, with m = n − 1 | `f▷ → 0▷`, `t▷ → ▷`, and the carry and left-end rules of T | 4 and 16 |
| T5 | n → n/2 or (5n + 1)/2 | the same construction in mixed binary and quinary, 17 rules | 13 and 17 |

Two observations.

**The shifted sibling needs no increment.** For 3n − 1 the right shift is m = n − 1, and the
halving step rounds *down*: `t▷ → ▷` simply deletes the digit. S⁻ therefore has the same 11-rule
shape as the paper's T, with no `s` at all. So in the shifted picture the Collatz system and
its looping sibling differ only in how the odd step rounds: S⁻ deletes the last digit, while S
rounds up, which is what the increment symbol and its rules `fs → t`, `ts → sf` and `◁s → ◁f`
are for. Whatever makes S terminate, if it does, has to involve those rules.

**There is no shifted 5n + 1 system.** The shift works for 3n ± 1 because the growing step
n → (3n ± 1)/2 has an integer fixed point, ∓1. The fixed point of n → (5n + 1)/2 is −1/3, so no
integer shift removes the added constant. The 5n + 1 control exists only in unshifted form.

## 6. How this differs from the sketch this work started from

- The sketch described the even step as a pure relabelling. That holds: it is `f▷ → 0▷`.
- The sketch said the shift needs "a few extra rules to stop at m = 2". The cost is larger:
  an increment symbol with three rules of its own, and either a two-digit context on the odd
  step (S) or a second left marker with five more left-end rules (S2). S has 15 rules against
  the 11 of T, and S2 has 18.
- The increment is cheap at run time. It moves left only through `t` digits and is absorbed
  by the first `f` it meets, whereas a ternary digit always travels to the left end of the
  string.
- The paper's own hybrid system L (its Section 3.3) also has an increment symbol. S and S2
  differ from it in keeping positional binary and ternary digits throughout.

## 7. Limits

- Lemmas C, D, E and the two theorems are ordinary written proofs. They are short and follow a
  published argument, but they have not been machine-checked.
- The simulation covers every rewrite sequence from the start strings listed in
  `results/phase1/summary.md`. It supports the lemmas on those instances and would have exposed
  a wrong rule; it cannot establish termination in general, which is the conjecture itself.
