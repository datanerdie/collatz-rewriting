# Dimension 2: structure of the carry rules, and a machine-assisted case analysis

Dimension 1 was settled by a written proof (`docs/dimension1.md`). Dimension 2 is harder for a
concrete reason: 2×2 matrices can represent the value of a string exactly. With

    f ↦ [[2,0],[0,1]]   t ↦ [[2,0],[1,1]]   0 ↦ [[3,0],[0,1]]   1 ↦ [[3,0],[1,1]]   2 ↦ [[3,0],[2,1]]

a row vector (n, 1) multiplied by the matrices of a digit string becomes (n′, 1), where n′ is
the number obtained by appending those digits. Every carry rule is then an equality. So in
dimension 2 the question is no longer whether the carries can be respected, but whether any
such representation can be combined with the end rules.

This note has two parts: a lemma about the carry rules that holds in every dimension, and a
case analysis for dimension 2 carried out by a solver. The status of each part is stated in
section 4.

## 1. The carry rules can be undone around a circle

Write M_x for the matrix of a symbol x in a natural matrix interpretation, and M_u for the
product of the matrices of a string u. For a carry rule ℓ → r every interpretation that makes
all rules weakly decreasing has M_ℓ ≥ M_r entrywise.

**Lemma I (carry rigidity).** In a natural matrix interpretation of any dimension under which
the six carry rules are weakly decreasing, for every carry rule ℓ → r and every string u of
digits,

    trace( M_u · (M_ℓ − M_r) ) = 0.

Since both factors have non-negative entries, this means (M_u)_{ik} · (M_ℓ − M_r)_{ki} = 0 for
all i and k. In particular (u empty) M_ℓ and M_r have the same diagonal.

*Proof.* Fix a length n and consider all strings of n digits written around a circle, with a
marked starting point. A carry rule replaces a binary digit followed by a ternary digit
("x d") by a ternary digit followed by a binary digit ("d′ x′"). The six rules

    f0 → 0f   f1 → 0t   f2 → 1f   t0 → 1t   t1 → 2f   t2 → 2t

have six different left sides and six different right sides: they are a one-to-one
correspondence between the pairs "binary, ternary" and the pairs "ternary, binary". So from a
circular string, the number of ways to apply a rule is the number of places where a binary
digit is followed by a ternary digit, and the number of ways it can have been produced by a
rule is the number of places where a ternary digit is followed by a binary digit. Around a
circle these two numbers are equal. In a finite directed graph in which every vertex has as
many incoming as outgoing edges, every edge lies on a directed cycle. So every application of
a carry rule to a circular string can be continued by further applications until the original
string returns.

The trace of a product of matrices does not change when the factors are rotated. If a circular
string s is rewritten to s′ by a rule ℓ → r, then after rotating, M_s = M_ℓ·M_u and
M_s′ = M_r·M_u, and trace(M_s) ≥ trace(M_s′) because M_ℓ ≥ M_r and M_u ≥ 0. Along a cycle of
rewrites the trace can never go up and it returns to its starting value, so it is constant.
Applying this to the circular string "ℓ u" gives trace(M_ℓ M_u) = trace(M_r M_u). ∎

**Corollary 1 (any dimension).** Call the digit matrices *irreducible* if for every pair of
coordinates i, k some product of them has a positive entry in position (i, k). If they are
irreducible, the matrix parts of all six carry rules are equalities:

    M_f M_0 = M_0 M_f    M_f M_1 = M_0 M_t    M_f M_2 = M_1 M_f
    M_t M_0 = M_1 M_t    M_t M_1 = M_2 M_f    M_t M_2 = M_2 M_t

So an irreducible interpretation contains an exact matrix representation of the arithmetic of
digit strings.

**Corollary 2 (dimension 2).** For 2×2 matrices and each carry rule ℓ → r:

- M_ℓ and M_r have the same diagonal;
- if some digit matrix has a positive entry above the diagonal, M_ℓ and M_r agree below the
  diagonal; if some digit matrix has a positive entry below the diagonal, they agree above it.

The lemma also holds for the right form, where the order of every product is reversed.

The lemma says nothing about the constant vectors of the interpretation. The corresponding
statement for the affine maps would need a circular string that contains the end markers, and
rewriting such a string in a circle is a cycle of the Collatz map.

## 2. What the solver is asked

For the system T, in each search form, the question is the one of Phase 3 with no bound on the
coefficients: is there a two-dimensional natural interpretation under which every rule is
weakly decreasing and some strict rule is strictly decreasing?

The solver z3 cannot answer this directly: the constraints are polynomial in about 40 unknown
integers, and z3 gives up even on variants that are known to have solutions. The question is
therefore split into cases.

1. **Zero patterns.** For each of the five digit matrices, fix which entries are zero. The
   patterns are restricted to those compatible with the carry rules, which is a finite check,
   and one of each pair related by exchanging the two coordinates is kept.
2. **Lemma I.** In each case the equalities of Corollary 2 are added. They are consequences of
   the other constraints, so they do not change the answer; they make it reachable.
3. **A weaker question.** Only the first row of the matrix of the end marker that carries the
   strict rules is kept (`◁` in the left form, `▷` in the right form). This discards
   constraints, so "no solution" for the weaker question implies "no solution" for the
   original.
4. **Two decision procedures.** First z3's integer solver, with a short time limit. For the
   cases it leaves undecided, the same constraints over the real numbers, with every entry
   that the pattern makes positive required to be at least 1. An integer solution is a real
   solution of this kind, so "no real solution" implies "no integer solution". For real
   polynomial constraints z3 has a complete procedure.

## 3. Results

The case analysis is still running; this section will be filled in when it finishes.

## 4. Status

- Lemma I and its corollaries are written proofs.
- The case analysis is not complete, so nothing is claimed yet about dimension 2.
