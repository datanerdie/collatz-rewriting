# Dimension 2: structure of the carry rules, and a machine-assisted case analysis

Dimension 1 was settled by a written proof (`docs/dimension1.md`). Dimension 2 is harder for a
concrete reason: 2×2 matrices can represent the value of a string exactly. With

    f ↦ [[2,0],[0,1]]   t ↦ [[2,0],[1,1]]   0 ↦ [[3,0],[0,1]]   1 ↦ [[3,0],[1,1]]   2 ↦ [[3,0],[2,1]]

a row vector (n, 1) multiplied by the matrices of a digit string becomes (n′, 1), where n′ is
the number obtained by appending those digits. Every carry rule is then an equality. So in
dimension 2 the question is no longer whether the carries can be respected, but whether any
such representation can be combined with the end rules.

This note has three parts: a lemma about the carry rules that holds in every dimension, a
simplification of the end markers, and a case analysis for dimension 2 carried out by a
solver. The status of each part is stated in section 5.

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

## 2. The end markers can be simplified

Call the end marker that stands at the front of every strict rule the *top* marker: `◁` in
the left form, `▷` in the right form, where every string is written reversed. The checker
compares the interpretations of the two sides of a rule entry by entry, and for a strict rule
additionally requires the first entry of the vector to decrease.

**Lemma II.** Suppose a natural matrix interpretation of dimension d makes every rule of T
weakly decreasing and a strict rule ρ strictly decreasing, in one of the two forms. Then so
does the interpretation obtained from it by

- keeping the first row of the matrix of the top marker and replacing its other rows and its
  vector by zero, and
- replacing the matrix of the other end marker by zero and keeping its vector.

*Proof.* The digits are not changed, so the carry rules are not affected. A strict rule has
the form "top u → top w" with strings u, w that do not contain the top marker. Write (M, v)
for the interpretation of the top marker and (M_u, v_u), (M_w, v_w) for those of u and w. The
rule is weakly decreasing when M·M_u ≥ M·M_w and v + M·v_u ≥ v + M·v_w, that is,
M·v_u ≥ M·v_w, and strictly decreasing when the first entries of these vectors differ. Each
row of M enters these conditions separately and v does not enter at all. So they remain true
when rows other than the first are replaced by zero and v is replaced by zero, and the first
row, which decides strictness, is unchanged. The remaining rules have the form "u other →
w other" with digit strings u, w (w may be empty). With (N, n) for the other marker they
require M_u·N ≥ M_w·N and v_u + M_u·n ≥ v_w + M_w·n. Replacing N by zero makes the first
condition trivial and does not touch the second. ∎

So, in dimension 2, the question is whether there are five digit interpretations (M_x, v_x),
a row r ≥ 0 and a column n ≥ 0 with the following properties. In the left form (writing
A, B, E, F, G for the matrices of f, t, 0, 1, 2 and a, b, e, f, g for their vectors):

    the six carry rules:      M_x·M_y ≥ M_z·M_w  and  v_x + M_x·v_y ≥ v_z + M_z·v_w
    f▷ → ▷,  t▷ → 2▷:         a + A·n ≥ n          b + B·n ≥ g + G·n
    ◁0 → ◁t:                  r·E ≥ r·B            r·e ≥ r·b
    ◁1 → ◁ff:                 r·F ≥ r·A·A          r·f ≥ r·(a + A·a)
    ◁2 → ◁ft:                 r·G ≥ r·A·B          r·g ≥ r·(a + A·b)

with at least one of the last three vector inequalities strict. The right form is the same
with every product reversed, the roles of the two end markers exchanged, and the two rules
for `▷` as the strict ones. A solution of these conditions is an interpretation, so nothing
is lost and nothing is gained: the conditions have a solution exactly when T has a
two-dimensional natural interpretation that removes a rule.

## 3. What the solver is asked

The solver z3 cannot decide these conditions as they stand: they are polynomial inequalities
in 34 unknown integers, and z3 gives up. The question is therefore split into cases.

1. **Zero patterns.** For each of the five digit matrices, fix which entries are zero. A
   pattern is dropped if it contradicts the matrix part of a carry rule (an entry that is
   positive on the right must be positive on the left), which is a finite check. Exchanging
   the two coordinates turns a solution into a solution, so of two patterns related in this
   way one is kept.
2. **Lemma I.** In each case the equalities of Corollary 2 are added, and with them what
   follows by dividing out factors that the pattern makes positive: from x·y = x·z and x > 0,
   y = z. The division is done by a computer algebra system and every factorisation is
   checked by multiplying it out. These equalities are consequences of the other conditions,
   so they do not change the answer; they make it reachable.
3. **The whole pattern, over the integers.** z3 is given the case as one problem.
4. **Parts.** A case that z3 leaves undecided is split by which entries of the row r are zero
   (three possibilities, since r = 0 cannot make a rule strict) and by which strict rule is
   strictly decreasing. Each part is tried over the integers and then over the real numbers.
   Over the reals, every entry that the pattern makes positive is required to be at least 1,
   r is scaled so that its smallest positive entry is 1, and the strict rule is required to
   decrease by at least 1. An integer solution gives a real solution of this kind: r can be
   scaled because every condition on it is homogeneous, and afterwards all vectors can be
   multiplied by a common factor to restore the decrease. So "no real solution" implies "no
   integer solution". For real polynomial constraints z3 has a complete procedure; whether it
   finishes in the time allowed is another matter.

A case is *refuted* when z3 reports that no solution exists, for the whole pattern or for
every part. If z3 reports an integer solution, it is turned into a certificate and given to
`checker/check.py`. Otherwise the case is *undecided*.

`harness/dimension2.py --selftest` checks the encoding in two ways. The representation of the
value of a string given at the top of this note satisfies every weak condition, in both
forms, and its transpose does not, which tests the order of every product. And for two
smaller systems that do have a proof (T without `t▷ → 2▷` in the left form, T without the
left-end rules in the right form) the same procedure finds an interpretation that the checker
accepts.

## 4. Results

The case analysis with the final version of the script is running; this section will be
filled in when it finishes.

## 5. Status

- Lemma I, its corollaries and Lemma II are written proofs.
- The case analysis is not complete, so nothing is claimed yet about dimension 2.
