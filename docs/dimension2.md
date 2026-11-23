# Dimension 2: structure of the carry rules, and a machine-assisted case analysis

Dimension 1 was settled by a written proof (`docs/dimension1.md`). Dimension 2 is harder for a
concrete reason: 2×2 matrices can represent the value of a string exactly. With

    f ↦ [[2,0],[0,1]]   t ↦ [[2,0],[1,1]]   0 ↦ [[3,0],[0,1]]   1 ↦ [[3,0],[1,1]]   2 ↦ [[3,0],[2,1]]

a row vector (n, 1) multiplied by the matrices of a digit string becomes (n′, 1), where n′ is
the number obtained by appending those digits. Every carry rule is then an equality. So in
dimension 2 the question is no longer whether the carries can be respected, but whether any
such representation can be combined with the end rules.

This note has five parts: a lemma about the carry rules that holds in every dimension, a
simplification of the end markers, two theorems that exclude the interpretations in which
the digit t or the digit 2 mixes the coordinates (one in every dimension, a stronger one in
dimension 2), a description of the digit matrices when the digit f mixes the coordinates,
with a theorem that excludes those interpretations, and a case analysis for the rest of
dimension 2 carried out by a solver. The
status of each part is stated in section 7.

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

In the right form, with m ≥ 0 for the vector of `◁` and r for the first row of the matrix of
`▷`, the conditions used below are

    2f → f1 (the carry rule f2 → 1f):   G·A ≥ A·F        g + G·a ≥ a + A·f
    1t → f2 (the carry rule t1 → 2f):   F·B ≥ A·G        f + F·b ≥ a + A·g
    2t → t2 (the carry rule t2 → 2t):   G·B ≥ B·G        g + G·b ≥ b + B·g
    2◁ → tf◁:                                             g + G·m ≥ b + B·a + B·A·m
    ▷f → ▷:                             r·A ≥ r           r·a ≥ 0
    ▷t → ▷2:                            r·B ≥ r·G         r·b ≥ r·g

and a strict rule means r·a > 0 or r·b > r·g.

## 3. Interpretations in which the digit t or the digit 2 mixes the coordinates

This section is proved in writing and holds in every dimension d. The vectors of f, t, 0, 1,
2 are written a, b, e, f, g as above, and r, n, m are the row and the vectors of section 2.

**Lemma III (left form).** If the vector g of the digit 2 is zero, no rule is strict.

*Proof.* The carry rule f2 → 1f gives a + A·g ≥ f + F·a, so with g = 0, f ≤ a entry by
entry. The rule ◁2 → ◁ft gives r·g ≥ r·a + r·A·b, so r·a = 0 and the rule is not strict.
Then r·f ≤ r·a = 0, and ◁1 → ◁ff, which says r·f ≥ r·a + r·A·a, gives r·A·a = 0 and is not
strict. The carry rule f1 → 0t gives a + A·f ≥ e + E·b ≥ e, so
r·e ≤ r·a + r·A·f ≤ r·a + r·A·a = 0. So both sides of r·e ≥ r·b are zero and ◁0 → ◁t is not
strict. ∎

Three standard facts about a square matrix B with non-negative entries that is irreducible
(for every i, k some power of B has a positive entry at (i, k)) are used:

- its spectral radius β is an eigenvalue with a left eigenvector y and a right eigenvector x
  whose entries are all positive;
- every left eigenvector of B with non-negative entries is a multiple of y, and every such
  right eigenvector a multiple of x;
- if the entries of B are integers, β ≥ 1. (Some power B^k has a positive diagonal entry, so
  the trace of B^(k·j) is at least 1 for every j, and it is at most d·β^(k·j).)

*A matrix that commutes with B.* If G has non-negative entries and B·G = G·B, then
y·G = γ·y and G·x = γ·x for one number γ ≥ 0. Indeed (y·G)·B = (y·B)·G = β·(y·G), so y·G is
zero or a non-negative left eigenvector of B, hence a multiple γ·y. In the same way
G·x = γ′·x, and y·G·x = γ·(y·x) = γ′·(y·x) with y·x > 0.

**Theorem 5.** Let d ≥ 1. There is no natural matrix interpretation of dimension d that
makes every rule of T weakly decreasing and a strict rule strictly decreasing

- *(left form)* if the matrix of t or the matrix of 2 is irreducible, the matrix A of f is
  entrywise at least the identity matrix, and no row of A − I is zero;
- *(right form)* if the matrix B of t is irreducible with spectral radius greater than 1, the
  matrix A of f is entrywise at least the identity matrix, and no column of A − I is zero.

In particular there is none, in either form and for d ≥ 2, in which no entry of the matrices
of f and t is zero. (For d = 2 the spectral radius of an irreducible integer matrix is 1
only for the matrix that exchanges the two coordinates.)

*Proof, left form.* An irreducible matrix among the digits makes the digit matrices
irreducible in the sense of Corollary 1, so B·G = G·B. Let y, x be the positive eigenvectors
of whichever of B, G is irreducible. By the remark on commuting matrices y·B = β·y,
B·x = β·x, y·G = γ·y, G·x = γ·x with β, γ ≥ 0, and β ≥ 1 if B is the irreducible one, γ ≥ 1
if G is.

*γ > β and γ ≥ 1.* The row r is not zero, since otherwise no rule is strict. Because A ≥ I,
r·A − r = r·(A − I) ≥ 0; and it is not zero, because some r_i is positive and row i of A − I
is not zero. As x is positive, r·A·x > r·x > 0. The matrix part of ◁2 → ◁ft is
r·G ≥ r·A·B; multiplied by x it reads γ·(r·x) ≥ β·(r·A·x). If β > 0 this gives
γ·(r·x) > β·(r·x), so γ > β. If β = 0 then B is not irreducible, so G is, and γ ≥ 1 > β. In
both cases γ ≥ 1.

*g = 0.* For a vector v write λ(v) = y·v ≥ 0. Multiplying the vector parts of t2 → 2t and of
t▷ → 2▷ by y gives

    λ(b) + β·λ(g) ≥ λ(g) + γ·λ(b)        λ(b) + β·λ(n) ≥ λ(g) + γ·λ(n).

The second gives λ(b) ≥ λ(g) + (γ − β)·λ(n) ≥ λ(g). The first is
(β − 1)·λ(g) ≥ (γ − 1)·λ(b), and (γ − 1)·λ(b) ≥ (γ − 1)·λ(g) because γ ≥ 1. So
(γ − β)·λ(g) ≤ 0, hence λ(g) = 0, and g = 0 because y is positive. By Lemma III no rule is
strict. ∎

*Proof, right form.* Again B·G = G·B; let y, x be the positive eigenvectors of B, with
β > 1, y·G = γ·y and G·x = γ·x. The matrix part of ▷t → ▷2, multiplied by x, gives
β·(r·x) ≥ γ·(r·x), so β ≥ γ. Multiplying the vector parts of 2t → t2 and 2◁ → tf◁ by y gives

    (γ − 1)·λ(b) ≥ (β − 1)·λ(g)          λ(g) + γ·λ(m) ≥ λ(b) + β·λ(a) + β·(y·A·m).

Because A ≥ I and no column of A − I is zero, every entry of y·A − y = y·(A − I) is
positive; so y·A·m ≥ λ(m), with equality only for m = 0. Put

    Δ = β·λ(a) + β·(y·A·m − λ(m)) + (β − γ)·λ(m),

a sum of three non-negative terms. The second inequality says λ(g) ≥ λ(b) + Δ. Then

    (γ − 1)·λ(b) ≥ (β − 1)·λ(g) ≥ (β − 1)·λ(b) + (β − 1)·Δ,

so 0 ≥ (β − γ)·λ(b) + (β − 1)·Δ. Both terms are non-negative and β > 1, so Δ = 0 and
(β − γ)·λ(b) = 0. From Δ = 0: λ(a) = 0, so a = 0 and ▷f → ▷ is not strict; and
y·A·m = λ(m), so m = 0.

- If β > γ, then λ(b) = 0, so b = 0, and r·b > r·g is impossible.
- If β = γ, then λ(b) ≥ λ(g) from the first inequality and λ(g) ≥ λ(b) from the second, so
  λ(g) = λ(b). With a = 0 and m = 0 the vector part of 2◁ → tf◁ is g ≥ b entry by entry.
  Since y is positive and y·(g − b) = 0, g = b, and ▷t → ▷2 is not strict. ∎

Theorem 5 does not cover a matrix of f that shares a row (in the right form, a column) with
the identity matrix. In dimension 1 the corresponding border case, a multiplier equal to 1,
also needed a separate argument. In dimension 2 the border cases can be settled.

**Theorem 6 (dimension 2).** In neither form is there a two-dimensional natural matrix
interpretation that makes every rule of T weakly decreasing and a strict rule strictly
decreasing, and in which

- the matrix of t or the matrix of 2 has both entries off the diagonal positive, and
- the matrix of f has both entries on the diagonal positive.

Notation for the proof. A ≥ I by the second condition. Let C be the one of B, G that is
irreducible and D the other; B·G = G·B by Corollary 1. Let y, x be the positive eigenvectors
of C, and β, γ ≥ 0 the numbers with y·B = β·y, B·x = β·x, y·G = γ·y, G·x = γ·x; the one that
belongs to C is at least 1. J is the matrix that exchanges the two coordinates. Three facts:

- (E) *If β = γ and r is a non-negative, non-zero row with r·B = r·G, then G = B or r is a
  positive multiple of y.* C is not a multiple of I, so every 2×2 matrix that commutes with
  it has the form u·I + w·C; thus D = u·I + w·C with u + w·β = β, and
  D − C = (1 − w)·(β·I − C). From r·(D − C) = 0: w = 1, which is D = C, or r·C = β·r, which
  makes r a non-negative left eigenvector of C.
- (J) *If β = γ = 1, then (B, G) is (J, J), (J, I) or (I, J).* C is an irreducible integer
  matrix with spectral radius 1, so C = J and y = (1, 1). D commutes with J, so it has equal
  diagonal entries u and equal off-diagonal entries w, with u + w = 1.
- (P) *It is impossible that all five digit matrices have y as a left eigenvector with
  eigenvalue 1 while r is a multiple of y.* Multiplying every vector condition by y would
  turn the interpretation into a one-dimensional one: multiplier 1 and constant y·v for a
  digit with vector v, multiplier 1 and constant 0 for the top marker, multiplier 0 and
  constant y·n (or y·m) for the other marker. Every rule stays weakly decreasing, and a
  strict rule stays strict because r is a multiple of y. This contradicts Theorem 4.

*Proof, left form.* As in the proof of Theorem 5, r·x > 0 and
γ·(r·x) = r·G·x ≥ r·A·B·x = β·(r·A·x) ≥ β·(r·x), now only because A ≥ I. So γ ≥ β. If γ > β,
then γ ≥ 1 and the second half of the proof of Theorem 5 applies word for word. So γ = β ≥ 1
and both inequalities are equalities. Since x is positive, r·A − r ≥ 0 and
r·G − r·A·B ≥ 0, this means

    r·A = r        and        r·G = r·A·B = r·B.

By (E), G = B or r is a positive multiple of y.

*If r is a positive multiple of y.* Then r·(A − I) = 0 with r positive forces A = I. The
carry equalities A·G = F·A and B·F = G·A become G = F and B·F = G, so B·G = G; multiplying
by y gives β·γ = γ, so β = γ = 1. Of the three pairs in (J) only B = I, G = J satisfies
B·G = G. Then F = G = J, and A·F = E·B gives E = J. All five matrices fix y = (1, 1), and
(P) gives a contradiction.

*If G = B.* The rule t▷ → 2▷ reads b + B·n ≥ g + B·n, so b ≥ g. The rule ◁2 → ◁ft reads
r·g ≥ r·a + r·A·b = r·a + r·b ≥ r·a + r·g. So r·a = 0, r·b = r·g, and this rule is not strict.
Multiplying the carry rules f2 → 1f and f1 → 0t by r, and using r·A = r and r·a = 0:

    r·g ≥ r·f + r·F·a ≥ r·f        r·f ≥ r·e + r·E·b ≥ r·e + r·B·b,

the last step by the matrix part r·E ≥ r·B of ◁0 → ◁t, whose vector part is r·e ≥ r·b.
Together: r·b = r·g ≥ r·f ≥ r·e + r·B·b ≥ r·b + r·B·b. Hence

    r·B·b = 0        and        r·f = r·e = r·b.

So ◁0 → ◁t is not strict, and ◁1 → ◁ff, which reads r·f ≥ r·a + r·A·a = 0, is strict only
if r·b > 0. Suppose r·b > 0. If both entries of r were positive, both entries of r·B would
be (B = G is irreducible), and r·B·b = 0 would give b = 0. So r has one positive entry;
after exchanging the coordinates, r = (r₁, 0). Then r·B = r₁·(B₁₁, B₁₂) with B₁₂ > 0, so
b₂ = 0, b₁ > 0 and B₁₁ = 0. From r·A = r the first row of A is (1, 0), and from r·E ≥ r·B,
E₁₂ ≥ B₁₂ > 0. The carry equality A·E = E·A reads E₁₂ = E₁₂·A₂₂ and
E₁₁ = E₁₁ + E₁₂·A₂₁ in the first row, so A₂₂ = 1 and A₂₁ = 0: A = I. Then G = F and
B·F = G as before, so B·B = B, hence β = 1 and B = J; but J·J = I. Contradiction. ∎

*Proof, right form.* The matrix part of ▷t → ▷2 gives
(r·B − r·G)·x = (β − γ)·(r·x) ≥ 0, so β ≥ γ. Exactly as in the proof of Theorem 5, using only
A ≥ I for y·A·m ≥ λ(m),

    λ(g) ≥ λ(b) + Δ,    (γ − 1)·λ(b) ≥ (β − 1)·λ(g),    0 ≥ (β − γ)·λ(b) + (β − 1)·Δ,

with Δ = β·λ(a) + β·(y·A·m − λ(m)) + (β − γ)·λ(m) ≥ 0.

*Case β > 1.* Then Δ = 0 and (β − γ)·λ(b) = 0. From Δ = 0: a = 0, so ▷f → ▷ is not strict;
and y·(A − I)·m = 0, so (A − I)·m = 0, that is, A·m = m. If β > γ, then b = 0 and ▷t → ▷2 is
not strict. If β = γ, then λ(b) = λ(g) as in Theorem 5, and r·B = r·G because
(r·B − r·G)·x = 0. By (E), r is a multiple of y, and then r·b − r·g is a multiple of
λ(b) − λ(g) = 0; or G = B, and then 2◁ → tf◁ reads g + B·m ≥ b + B·A·m = b + B·m, so g ≥ b,
and with λ(g) = λ(b), g = b. In both cases ▷t → ▷2 is not strict.

*Case β = 1.* Then γ ≤ 1. If G is the irreducible one, γ = 1. If B is, then B = J by the
argument of (J), G commutes with J, so it has equal diagonal entries u and equal off-diagonal
entries w, and γ = u + w is 0 or 1.

- γ = 0: then G = 0. The rule 2t → t2 gives g ≥ b + B·g, so λ(g) ≥ λ(b) + λ(g) and b = 0;
  ▷t → ▷2 is not strict. The rules 2f → f1 and 1t → f2 give g ≥ a + A·f ≥ a + f and
  f ≥ a + A·g ≥ a + g, so g ≥ 2·a + g and a = 0; ▷f → ▷ is not strict.
- γ = 1: by (J) there are three pairs (B, G). Write p, q, s, u for the entries of A, row by
  row; p, u ≥ 1. The carry equalities used are F·A = B·E, G·A = A·F, E·B = B·F, F·B = A·G.
  - B = G = J: F·J = A·J gives F = A, and then J·A = A·A. Its top right entry is
    u = q·(p + u). If q ≥ 1 the right side exceeds u; if q = 0, u = 0. Contradiction.
  - B = J, G = I: F·J = A gives F = A·J, and then A = A·F = A·A·J. Its top left entry is
    p = q·(p + u), a contradiction in the same way.
  - B = I, G = J: then E = F = A·J, and F·A = E gives A·J·(A − I) = 0. With N = A − I ≥ 0
    this is J·N + N·J·N = 0, so J·N = 0, N = 0 and A = I. So E = F = J. From
    (r·B − r·G)·x = 0, r = r·J, so r is a multiple of y = (1, 1). By (P), a contradiction. ∎

Theorem 6 needs a digit t or 2 that mixes the coordinates and a matrix of f with a positive
diagonal. The next section starts from the digit f instead.

## 4. Interpretations in which the digit f mixes the coordinates

This section is about dimension 2 and is proved in writing. Its first result concerns the
digit matrices alone: when the matrix of f mixes the two coordinates, the carry equalities
of Corollary 1 leave very few possibilities.

Throughout the section A is a 2×2 matrix with non-negative integer entries whose two entries
off the diagonal are positive. Such a matrix is irreducible. Notation and elementary facts:

- A has two real eigenvalues α > α′, because the discriminant (A₁₁ − A₂₂)² + 4·A₁₂·A₂₁ of its
  characteristic polynomial is at least 4. The larger one is the spectral radius, with a
  positive column x and a positive row y as eigenvectors. Since
  α = (trace + √discriminant)/2, α ≥ 1, and α = 1 only for A = J. Since α + α′ is the trace,
  α′ = −α only if both diagonal entries of A are zero.
- Π = x·y/(y·x) (a column times a row, divided by a number) satisfies A·Π = Π·A = α·Π and
  Π·Π = Π. All its entries are positive and its trace is 1, so its diagonal entries are
  less than 1. A = α·Π + α′·(I − Π).
- A is not a multiple of I, so a matrix that commutes with A has the form u·I + w·A. It is
  then ε·Π + ε′·(I − Π) for two numbers ε, ε′, and has x and y as eigenvectors with
  eigenvalue ε.
- A matrix M with non-negative entries and M·x = 0 or y·M = 0 is zero.
- If a column times a row equals another column times a row and the product is not zero,
  the two columns are multiples of each other and so are the two rows.

The six carry equalities, with A, B, E, F, G for the matrices of f, t, 0, 1, 2 in the order
of the left form, are numbered

    (1) A·E = E·A    (2) A·F = E·B    (3) A·G = F·A
    (4) B·E = F·B    (5) B·F = G·A    (6) B·G = G·B

**Theorem 7 (the digit matrices when f mixes the coordinates).** Let A, B, E, F, G be 2×2
matrices with non-negative integer entries that satisfy (1) to (6), where both entries off
the diagonal of A are positive. Then one of the following holds, with ε the eigenvalue of E
on x and y.

- (S0) F = G = 0.
- (S1) x and y are eigenvectors of all five matrices, with eigenvalues α, α, ε, ε, ε for
  A, B, E, F, G, and ε > 0.
- (S2) det A > 0; y is a left eigenvector of all five matrices with eigenvalues
  α, α, ε, ε, ε, and ε > 0; the eigenvalues of A and those of B are α and α/2, and the
  eigenvalues of each of E, F, G are ε and ε/3.
- (S3) det A = 0; ε > 0; F·x = ε·x, y·G = ε·y and y·B = (α/ε)·(y·F); and there is a
  positive row ỹ with ỹ·B = α·ỹ and ỹ·G = ε·ỹ, namely ỹ = y if y·F = ε·y, and otherwise
  ỹ = y·F, in which case the diagonal of F is zero and F·F = ε²·I.

In the proof, (S2) arises from the relations τ·A = A·τ·τ and τ·E = E·τ·τ·τ for
τ = B·A⁻¹. The value representation at the top of this note satisfies them, up to the
order of the products: there τ adds 1 to the number, and the relations say
2·(n + 1) = 2·n + 2 and 3·(n + 1) = 3·n + 3. Its matrix of f is diagonal, so it is not
covered by the theorem itself but by Corollary 10 below, which says: when the matrices of
f, t and 0 are invertible, the six carry equalities force either t = f, or this arithmetic.
The smallest example of (S2) has A = [[3, 1], [1, 3]] and B = [[4, 2], [0, 2]].

*Proof.* If F = 0, then A·G = 0 by (3), so α·(y·G) = 0 and G = 0: this is (S0). Assume
F ≠ 0. By (1), E = ε·Π + ε′·(I − Π).

*First case: det A ≠ 0.* By (2) and (3), F = A⁻¹·E·B and G = A⁻¹·F·A. So E ≠ 0 and B ≠ 0,
and ε > 0 because E·x = ε·x.

(a) *E is singular.* Then ε′ = 0 and E = ε·Π, so F = (ε/α)·Π·B. Equality (4), multiplied by
α·(y·x)/ε, reads α·(B·x)·y = x·(y·B·B). Here B·x ≠ 0. So B·x = β·x with β > 0, and
y·B·B = α·β·y; multiplying this by x gives β² = α·β. So B·x = α·x and y·B·B = α²·y. Put
z = y·B, so that z·x = α·(y·x). Now G = (ε/α²)·Π·B·A, and (5) reads
ε·x·z = (ε/α²)·x·(z·A·A), so z·A·A = α²·z.

*z = α·y.* If α′ ≠ −α: from A·A = α²·Π + α′²·(I − Π), z·A·A = α²·z says z·(I − Π) = 0, so
z = z·Π = α·y. If α′ = −α, the diagonal of A is zero. From y·B·B = α²·y,
y·(B − α·I)·(B + α·I) = 0. If −α is not an eigenvalue of B this gives y·B = α·y. If it is,
the eigenvalues of B are α and −α, its trace is zero, so its diagonal is zero too; then
B·x = α·x = A·x determines both entries off the diagonal, B = A, and again y·B = α·y.

With z = α·y: F = (ε/α)·x·z/(y·x) = ε·Π and G = (ε/α²)·x·(z·A)/(y·x) = ε·Π. This is (S1).

(b) *E is invertible.* Put τ = B·A⁻¹, τ₁ = A⁻¹·τ·A, τ₂ = A⁻²·τ·A² and θ = E⁻¹·τ·E. The last
three are similar to τ. Substitute B = τ·A, F = A⁻¹·E·τ·A and G = A⁻²·E·τ·A² into (4), (5)
and (6), multiply on the left by E⁻¹·A, E⁻¹·A², E⁻¹·A² and on the right by A⁻¹, A⁻³, A⁻³
respectively, and use that E commutes with A. The result is

    A·θ = τ·A·τ        A²·θ·τ·A⁻² = τ        A²·θ·A⁻¹·τ·A⁻¹ = τ·A²·τ·A⁻²

that is,

    θ = τ₁·τ        θ·τ = τ₂        θ·τ₁ = τ₂·τ.                                  (∗)

- *B is invertible.* Then so are τ, τ₁, τ₂. From (∗), τ₂ = τ₁·τ·τ and
  τ₁·τ·τ₁ = τ₂·τ = τ₁·τ·τ·τ; cancelling, τ₁ = τ·τ and then θ = τ·τ·τ. So τ is similar to
  its square and to its cube, and its pair of eigenvalues (complex numbers, not zero) is
  unchanged by squaring and by cubing. If squaring fixes each of them, both are 1. If it
  exchanges them, λ₁⁴ = λ₁, so λ₁³ = 1 and likewise λ₂³ = 1; cubing then turns the pair
  into (1, 1), so again both are 1. Hence N = τ − I satisfies N·N = 0, τ·τ = I + 2·N, and
  τ₁ = τ·τ becomes N·A = 2·A·N.

  If N = 0, then B = A, F = A⁻¹·E·A = E and G = E. E commutes with A: this is (S1).

  If N ≠ 0, write N = c·d with a column c and a row d; d·c = 0 because N·N = 0. Then
  N·A = 2·A·N reads c·(d·A) = 2·(A·c)·d, and the left side is not zero. So A·c = μ·c and
  d·A = 2·μ·d with a real μ ≠ 0: the eigenvalues of A are μ and 2·μ. The spectral radius
  α > 0 is one of them, so μ > 0, α = 2·μ, α′ = α/2 and det A = α²/2 > 0. The row d is a
  left eigenvector for α, hence a multiple of y; after rescaling c, d = y. Then
  B = τ·A = A + α·c·y, so y·B = α·y and B·c = (α/2)·c. Also
  y·F = y·A⁻¹·E·B = ε·y and y·G = y·A⁻¹·F·A = ε·y. In the same way θ = τ·τ·τ = I + 3·N
  becomes N·E = 3·E·N, that is c·(y·E) = 3·(E·c)·y, so E·c = (ε/3)·c; and then
  F·c = A⁻¹·E·B·c = (ε/3)·c and G·c = A⁻¹·F·A·c = (ε/3)·c. This is (S2).

- *B is singular.* B ≠ 0, so τ has rank one: τ·τ = κ·τ with κ the trace of τ. From (∗),
  τ₂ = θ·τ = τ₁·τ·τ = κ·τ₁·τ = κ·θ. Both τ₂ and θ are similar to τ, so they are not zero
  and have trace κ; hence κ ≠ 0 and κ = κ², κ = 1. Write τ = c·w with w·c = 1. Then
  τ₁ = (A⁻¹·c)·(w·A), τ₂ = (A⁻²·c)·(w·A²) and θ = τ₁·τ = (w·A·c)·(A⁻¹·c)·w. From θ = τ₂,
  A⁻²·c is a multiple of A⁻¹·c, so A·c = μ·c with μ ≠ 0; then θ = c·w = τ. The third
  relation in (∗) is now τ·τ₁ = τ·τ = τ, that is (1/μ)·c·(w·A) = c·w, so w·A = μ·w. So c
  and w are a right and a left eigenvector of A for the same eigenvalue, with w·c = 1:
  τ is Π if μ = α, and I − Π if μ = α′. And B = τ·A = μ·τ. The matrix α′·(I − Π) has
  entries −α′·Π₁₂ and α′·(1 − Π₁₁), which are not both non-negative since α′ ≠ 0. So
  B = α·Π, and F = A⁻¹·E·B = ε·Π, G = A⁻¹·F·A = ε·Π. This is (S1).

*Second case: det A = 0.* Then α′ = 0, A = α·Π, every entry of A is positive, and α is the
trace of A, at least 2. Equality (3) reads x·(y·G) = (F·x)·y, and F·x ≠ 0; so F·x = φ·x and
y·G = φ·y with φ > 0. Multiplying (2) by y on the left gives α·(y·F) = ε·(y·B); as y·F ≠ 0,
ε > 0 and y·B = (α/ε)·(y·F). Multiplying (5) by y on the left gives
y·B·F = y·G·A = φ·α·y, so y·F·F = φ·ε·y; multiplying by x, φ² = φ·ε. So φ = ε:

    F·x = ε·x        y·G = ε·y        y·F·F = ε²·y        y·B = (α/ε)·(y·F).

If −ε is not an eigenvalue of F, then y·(F − ε·I)·(F + ε·I) = 0 gives y·F = ε·y, so
y·B = α·y, and ỹ = y has the properties in (S3). If −ε is an eigenvalue of F, its
eigenvalues are ε and −ε, its trace is zero, so its diagonal is zero, its two other entries
are positive, and F·F = ε²·I. Put ỹ = y·F, a positive row, so that y·B = (α/ε)·ỹ. Multiplying
(6) by y on the left: y·B·G = y·G·B = ε·(y·B), so ỹ·G = ε·ỹ. Multiplying (5), which reads
B·F = α·(G·x)·y/(y·x), by F on the right: ε²·B = α·(G·x)·ỹ/(y·x). Hence
ỹ·B = α·(ỹ·G·x)/(ε²·(y·x))·ỹ = α·(y·F·x)/(ε·(y·x))·ỹ = α·ỹ. This is (S3). ∎

`harness/theorem7_check.py` lists every solution of (1) to (6) with entries up to a bound
and tests the four cases on each; with entries up to 3 there are 39,396 solutions and each
is in one of the cases (`results/dimension2/theorem7-check.md`). With the option `--z3` it
also tests Theorem 8 below on the same solutions. These are checks of the statements on
small examples, not part of the proofs.

One part of the proof does not need a matrix of f that mixes the coordinates.

**Corollary 10 (dimension 2, both forms).** Let A, B, E, F, G be real 2×2 matrices that
satisfy (1) to (6), and let A, B and E be invertible.

- If B = A, then E = F = G.
- If B ≠ A, there are a column c, a row d with d·c = 0, and real numbers μ ≠ 0, ν ≠ 0 such
  that B = A + 2·μ·c·d; c is a right eigenvector of A and B with eigenvalue μ and of E, F,
  G with eigenvalue ν; and d is a left eigenvector of A and B with eigenvalue 2·μ and of
  E, F, G with eigenvalue 3·ν. In particular B has the trace and the determinant of A,
  with 2·(trace A)² = 9·det A, and F and G have the trace and the determinant of E, with
  3·(trace E)² = 16·det E.

If instead the six equalities hold with every product reversed, the same is true with
rows and columns exchanged (c a row, d a column, "left" and "right" exchanged); the
statements about traces and determinants are unchanged.

By Corollary 1 this applies to every interpretation in which the digit matrices are
irreducible (for instance one of them triangular upward and another downward, each with a
positive entry off the diagonal) and those of f, t and 0 are invertible.

*Proof.* If B = A, then (2) and (1) give A·F = E·A = A·E, so F = E, and (3) gives
A·G = F·A = A·E, so G = E. Let B ≠ A. In the proof of Theorem 7, the part "(b), B is
invertible" uses of A only that it is invertible, as far as the statement that N = τ − I
satisfies N·N = 0, N·A = 2·A·N and τ·τ·τ = E⁻¹·τ·E. Here N ≠ 0 because B ≠ A, and as
there N = c·d with d·c = 0, A·c = μ·c and d·A = 2·μ·d with a real μ ≠ 0. Then
B = τ·A = A + 2·μ·c·d, so B·c = μ·c and d·B = 2·μ·d. In the same way N·E = 3·E·N gives
E·c = ν·c and d·E = 3·ν·d with a real ν ≠ 0, and then F = A⁻¹·E·B and G = A⁻¹·F·A satisfy
F·c = ν·c, d·F = 3·ν·d, G·c = ν·c and d·G = 3·ν·d. The eigenvalues of A and B are thus μ
and 2·μ, with sum 3·μ and product 2·μ², and those of E, F, G are ν and 3·ν, with sum 4·ν
and product 3·ν². For the reversed equalities, apply this to the transposed matrices. ∎

**Theorem 8 (dimension 2).** In neither form is there a two-dimensional natural matrix
interpretation that makes every rule of T weakly decreasing and a strict rule strictly
decreasing, and in which

- both entries off the diagonal of the matrix of f are positive; or
- the digit matrices are irreducible in the sense of Corollary 1 and the matrices of f, t
  and 0 are invertible.

The proof for the left form uses two steps. The first is taken from the proof of Theorem 5.

- (L) *In the left form, if a positive row ỹ satisfies ỹ·B = β·ỹ and ỹ·G = γ·ỹ with γ > β
  and γ ≥ 1, no rule is strict.* This is the part "g = 0" of the proof of Theorem 5, which
  uses the row only through these properties.
- (V) *In the left form, if the digit matrices are irreducible, A, B and E are invertible
  and B ≠ A, no rule is strict.*

*Proof of (V).* By Corollary 1 the equalities (1) to (6) hold. By Corollary 10 there are a
column c, a row d with d·c = 0, and real numbers μ ≠ 0, ν ≠ 0 such that
A·c = μ·c, B = A + 2·μ·c·d, and d is a left eigenvector of A and B with eigenvalue 2·μ and
of E, F and G with eigenvalue 3·ν.

The spectral radius of A is one of its eigenvalues μ and 2·μ, so μ > 0; put α = 2·μ. The
trace 3·μ and the determinant 2·μ² of A are integers, so μ is an integer (if 3·μ = k, then
2·k²/9 is an integer and 3 divides k) and α ≥ 2. A matrix with non-negative entries has a
left and a right eigenvector with non-negative entries for its spectral radius. Since α is
a simple eigenvalue of A, d is a multiple of such a row, and after rescaling c its entries
are non-negative. If one of them were zero, the five equations d·M = (eigenvalue)·d would
give every digit matrix a zero at the same place off the diagonal, and the digit matrices
would not be irreducible. So d is positive. Write y for it and ε = 3·ν; then y·B = α·y and
y·G = ε·y. Moreover ε > 0, because y·E = ε·y, y is positive, and E has non-negative
entries and is not zero.

Let x₀ be an eigenvector of A for α with non-negative entries, c′ = (y·x₀)·c, and
x_t = x₀ + t·c′ for a number t. Then y·x_t = y·x₀ > 0,

    A·x_t = α·x_{t/2}        B·x_t = A·x_t + α·c·(y·x_t) = α·x_{t/2+1}.

In particular B·x₂ = α·x₂. The eigenvalues of B are α and α/2, so x₂ is a multiple of a
vector with non-negative entries, and has non-negative entries itself because y·x₂ > 0. E
commutes with A, so E·x₀ is a multiple of x₀, and multiplying by y shows E·x₀ = ε·x₀; in
the same way G·x₂ = ε·x₂, by (6).

Put ρ_t = r·x_t, so ρ₀ ≥ 0, ρ₂ ≥ 0 and ρ₁ = (ρ₀ + ρ₂)/2. The matrix parts of ◁0 → ◁t and
◁2 → ◁ft, multiplied by x₀ and by x₂, give

    ε·ρ₀ ≥ r·B·x₀ = α·ρ₁        ε·ρ₂ ≥ r·A·B·x₂ = α·(r·A·x₂) = α²·ρ₁.

Suppose ε ≤ α. The first inequality gives ρ₁ ≤ ρ₀, hence ρ₂ ≤ ρ₁. The second then gives
α²·ρ₁ ≤ ε·ρ₂ ≤ α·ρ₁, so ρ₁ = 0 because α ≥ 2, and ρ₀ = ρ₂ = 0. The row r is not zero; at a
coordinate where it is positive, x₀ and x₂ are both zero, so both are multiples of the
other unit vector, and c′ = (x₂ − x₀)/2 is a multiple of x₀. That is impossible, because c′
and x₀ are eigenvectors of A for different eigenvalues. So ε > α ≥ 2, and (L) applies with
ỹ = y, β = α, γ = ε. ∎

*Proof, left form, first statement.* The digit matrices are irreducible, so (1) to (6) hold
by Corollary 1 and Theorem 7 applies. The row r is not zero, so r·x > 0. The matrix part of
◁1 → ◁ff is r·F ≥ r·A·A; multiplied by x it gives r·F·x ≥ α²·(r·x) > 0. So F ≠ 0, which
excludes (S0), and whenever F·x = ε·x, ε ≥ α².

*(S1).* If α > 1, then ε ≥ α² > α, and (L) applies with ỹ = y, β = α, γ = ε. If α = 1,
then A = J, x and y are (1, 1), and ε ≥ 1. If ε > 1, (L) applies again. If ε = 1, every
digit matrix has non-negative integer entries with all row sums and column sums equal to 1,
so it is I or J. The rule ◁1 → ◁ff requires r·F ≥ r·A·A = r. If F = J this means that the
two entries of r are equal. If F = I, then (3) gives G = I, (5) gives B = J, (2) gives
E = I, and ◁0 → ◁t requires r = r·E ≥ r·B = r·J, so again the entries of r are equal. In
both cases r is a multiple of y and all five matrices fix y, which (P) in the proof of
Theorem 6 excludes. (The argument for (P) uses of y only that it is a positive row; here
y = (1, 1), so the one-dimensional interpretation it produces has integer coefficients, as
Theorem 4 requires.)

*(S3).* Here α ≥ 2 and ε ≥ α² > α, and (L) applies with the row ỹ, β = α, γ = ε.

*(S2).* The eigenvalues of A, B and E are not zero, so these matrices are invertible. If
B ≠ A, (V) applies. If B = A, then E = F = G by Corollary 10, and since E commutes with A
this is the situation of (S1). ∎

*Proof, left form, second statement.* If B ≠ A, this is (V). If B = A, then E = F = G by
Corollary 10, and E commutes with A by (1). If both entries off the diagonal of A are
positive, the first statement applies. Otherwise A is triangular or diagonal. If A is not a
multiple of I, then E = u·I + w·A is triangular in the same direction, or diagonal, and
the digit matrices are not irreducible. So A = B = s·I with an integer s ≥ 1, and
E = F = G has both entries off the diagonal positive. Theorem 6 excludes this. ∎

In the right form the carry equalities hold with every product reversed:

    (1′) E·A = A·E    (2′) F·A = B·E    (3′) G·A = A·F
    (4′) E·B = B·F    (5′) F·B = A·G    (6′) G·B = B·G

So the transposed matrices satisfy (1) to (6), and Theorem 7 and Corollary 10 apply to
them. What they provide for the matrices themselves is obtained by exchanging rows with
columns. Write λ(v) = y·v when a positive row y is given. Three steps are used.

- (Z) *In the right form, if F = G = 0 and both entries off the diagonal of A are positive,
  no rule is strict.* The rules 2f → f1 and 1t → f2 give g ≥ a + A·f and f ≥ a + A·g, so
  g ≥ a + A·A·g and, with the positive row y of A, λ(g) ≥ λ(a) + α²·λ(g). As α ≥ 1,
  λ(a) = 0 and a = 0. The rule 2t → t2 gives g ≥ b + B·g ≥ b. So r·a = 0 and r·b ≤ r·g.
- (C) *In the right form, if a positive row y is a left eigenvector of the five digit
  matrices with eigenvalues α, α, ε, ε, ε for A, B, E, F, G, where α > 1, and a positive
  column x̂ satisfies B·x̂ = α·x̂ and G·x̂ = ε·x̂, no rule is strict.* The matrix part of
  ▷t → ▷2, multiplied by x̂, gives α·(r·x̂) ≥ ε·(r·x̂), so α ≥ ε. Multiplying the vector
  parts of 2t → t2 and 2◁ → tf◁ by y,

      (ε − 1)·λ(b) ≥ (α − 1)·λ(g)        λ(g) ≥ λ(b) + Δ,   Δ = α·λ(a) + (α² − ε)·λ(m) ≥ 0,

  so 0 ≥ (α − ε)·λ(b) + (α − 1)·Δ and Δ = 0. Hence a = 0 and, because α² > α ≥ ε, m = 0.
  The rule 2◁ → tf◁ then reads g ≥ b. So r·a = 0 and r·b ≤ r·g.
- (V′) *In the right form, if the digit matrices are irreducible, A, B and E are invertible
  and B ≠ A, no rule is strict.*

*Proof of (V′).* Corollary 10, in its form for reversed products, gives a
column x, a row w with w·x = 0, and real numbers μ ≠ 0, ν ≠ 0 such that w·A = μ·w,
B = A + 2·μ·x·w, x is a right eigenvector of A and B with eigenvalue 2·μ and of E, F, G
with eigenvalue 3·ν, and w is a left eigenvector of A and B with eigenvalue μ and of E, F,
G with eigenvalue ν. As in the proof of (V): μ is a positive integer; with α = 2·μ ≥ 2, x
can be taken positive; and ε = 3·ν > 0. Moreover the trace 4·ν and the determinant 3·ν² of
E are integers, so ν is an integer (if 4·ν = k, then 3·k²/16 is an integer and 4 divides
k), and ε ≥ 3.

Let y₀ be a left eigenvector of A for α with non-negative entries, w′ = (y₀·x)·w and
y_t = y₀ + t·w′. Then y_t·x = y₀·x > 0, y_t·A = α·y_{t/2} and y_t·B = α·y_{t/2+1}. So
y₂·B = α·y₂, and as in the proof of (V) the entries of y₂, and those of y₁ = (y₀ + y₂)/2,
are non-negative, and y₂·G = ε·y₂ by (6′). No two of the rows y₀, y₁, y₂ are multiples of
each other, because w′ ≠ 0 is a left eigenvector of A for another eigenvalue than y₀. Hence
a column v with non-negative entries for which two of the numbers y₀·v, y₁·v, y₂·v are
zero is zero: at a coordinate where v is positive both rows would vanish, and they would be
multiples of the same unit row. Write Λ_t(v) = y_t·v.

The matrix part of ▷t → ▷2, multiplied by x, gives α ≥ ε. Since α is even and ε ≥ 3,
α ≥ 4, so α²/2 > ε. Multiplying the vector parts of 2t → t2 and 2◁ → tf◁ by y₂, and using
y₂·B·A = α²·y₁,

    (ε − 1)·Λ₂(b) ≥ (α − 1)·Λ₂(g)
    Λ₂(g) + ε·Λ₂(m) ≥ Λ₂(b) + α·Λ₂(a) + α²·Λ₁(m).

With Λ₁(m) = (Λ₀(m) + Λ₂(m))/2 the second says Λ₂(g) ≥ Λ₂(b) + Δ for

    Δ = α·Λ₂(a) + (α²/2)·Λ₀(m) + (α²/2 − ε)·Λ₂(m) ≥ 0,

and then 0 ≥ (α − ε)·Λ₂(b) + (α − 1)·Δ. So Δ = 0: Λ₂(a) = 0, Λ₀(m) = Λ₂(m) = 0 and hence
m = 0; and (α − ε)·Λ₂(b) = 0. With m = 0 the rule 2◁ → tf◁ reads g ≥ b + B·a ≥ b, so
▷t → ▷2 is not strict. It remains to show r·a = 0.

*If α > ε.* Then Λ₂(b) = 0, and the first inequality gives Λ₂(g) = 0. The rule 2f → f1,
g + G·a ≥ a + A·f, multiplied by y₂, gives Λ₂(g) + ε·Λ₂(a) ≥ Λ₂(a) + α·Λ₁(f), so
Λ₁(f) = 0. The rule 1◁ → ff◁ with m = 0 gives f ≥ a, so Λ₁(a) = 0. With Λ₂(a) = 0, a = 0.

*If α = ε.* The rows y₂ and w are left eigenvectors of B for different eigenvalues, so
r = σ·y₂ + σ′·w for two numbers σ, σ′. Then r·B − r·G = σ′·(α/2 − ε/3)·w = σ′·(α/6)·w, and
the matrix part of ▷t → ▷2 says that this row is non-negative. But w ≠ 0 and w·x = 0 with
x positive, so w has a positive and a negative entry. Hence σ′ = 0, r = σ·y₂, and
r·a = σ·Λ₂(a) = 0. ∎

*Proof, right form, first statement.* Theorem 7 applies to the transposed matrices. Let x
and y be the positive column and row of A.

*(S0).* This is (Z).

*(S1)* reads the same for the matrices themselves: x and y are eigenvectors of all five,
with eigenvalues α, α, ε, ε, ε. If α > 1, (C) applies with x̂ = x. If α = 1, then A = J, x
and y are (1, 1), α ≥ ε as in (C), and ε, a positive row sum of E, is 1. So every digit
matrix is I or J; ▷f → ▷ requires r·J ≥ r, so r is a multiple of y, and (P) gives a
contradiction.

*(S2).* A, B and E are invertible. If B ≠ A, (V′) applies. If B = A, then E = F = G by
Corollary 10, and this is the situation of (S1).

*(S3).* Then det A = 0, α ≥ 2, and with x scaled so that y·x = 1, A·v = α·λ(v)·x for every
column v. Transposing the statement of (S3) gives ε > 0 and

    y·F = ε·y    G·x = ε·x    B·x = (α/ε)·F·x    E·x = ε·x    y·E = ε·y,

and that either F·x = ε·x, or the diagonal of F is zero and F·F = ε²·I; with x̂ = x in the
first case and x̂ = F·x in the second, x̂ is a positive column with B·x̂ = α·x̂ and
G·x̂ = ε·x̂. As in (C), α ≥ ε.

*First case, F·x = ε·x.* Then B·x = α·x. Put z = y·B, so z·x = α. If z = α·y, then (5′),
multiplied by y on the left, gives ε·z = α·(y·G), so y·G = ε·y; y is a left eigenvector of
all five matrices with eigenvalues α, α, ε, ε, ε, and (C) applies. Otherwise z is not a
multiple of y (a multiple β·y would have β = α, because z·x = α). Multiplying (4′) by y on the left gives ε·z = z·F; so F has the two
independent left eigenvectors y and z for ε, and F = ε·I. Write E = ε·Π + ε′·(I − Π). Then
B·E = ε·A + ε′·(B − A), and (2′) says that this equals F·A = ε·A; since B ≠ A, ε′ = 0 and
E = ε·Π. Now (4′) reads ε·x·z = ε·B, so B = x·z; (5′) reads ε·x·z = α·x·(y·G), so
y·G = (ε/α)·z; and (6′) reads ε·x·z = x·(z·G), so z·G = ε·z. These two values determine G:
G = (ε/α)·B. Altogether, with Λ(v) = z·v,

    A·v = α·λ(v)·x    E·v = ε·λ(v)·x    F·v = ε·v    B·v = Λ(v)·x    G·v = (ε/α)·Λ(v)·x

and Λ(x) = α. The entries of z = y·B are non-negative. Moreover z ≤ α²·y entry by entry: the diagonal entry α·x_i·y_i of A is a
positive integer, so 1/x_i ≤ α·y_i, and z_i·x_i ≤ z·x = α. So Λ(v) ≤ α²·λ(v) for every
non-negative column v.

Multiplying the vector parts of 2t → t2 and 2◁ → tf◁ by z, with z·B = α·z, z·G = ε·z and
z·B·A·m = α³·λ(m):

    (ε − 1)·Λ(b) ≥ (α − 1)·Λ(g)        Λ(g) ≥ Λ(b) + Δ,   Δ = α·Λ(a) + α³·λ(m) − ε·Λ(m).

Here Δ ≥ α·Λ(a) + α²·(α − ε)·λ(m) ≥ 0. So 0 ≥ (α − ε)·Λ(b) + (α − 1)·Δ, hence Δ = 0:
Λ(a) = 0, ε·Λ(m) = α³·λ(m), and (α − ε)·Λ(b) = 0. The rule 2◁ → tf◁ itself reads
g + (ε/α)·Λ(m)·x ≥ b + Λ(a)·x + α²·λ(m)·x, which is now g ≥ b. So ▷t → ▷2 is not strict,
and it remains to show a = 0.

If α > ε: Λ(b) = 0, so Λ(g) = 0 by the first inequality. The rule 2f → f1, multiplied by z,
gives Λ(g) + ε·Λ(a) ≥ Λ(a) + α²·λ(f), so λ(f) = 0 and f = 0. The rule 1◁ → ff◁,
f + F·m ≥ a + A·a + A·A·m, multiplied by y, gives ε·λ(m) ≥ (1 + α)·λ(a) + α²·λ(m), and
since ε < α², λ(a) = 0 and a = 0.

If α = ε: then Λ(m) = α²·λ(m). Multiplying by y the rules 0f → f0, 0◁ → t◁, 0t → t1,
2f → f1 and 1◁ → ff◁, and by z the rule 1t → f2:

    λ(a) ≥ λ(e)                          from  λ(e) + α·λ(a) ≥ λ(a) + α·λ(e)
    λ(e) ≥ λ(b)                          from  λ(e) + α·λ(m) ≥ λ(b) + Λ(m)
    Λ(f) ≤ λ(e) + (α − 1)·λ(b) ≤ α·λ(a)  from  λ(e) + α·λ(b) ≥ λ(b) + Λ(f)
    λ(g) ≥ λ(a) + α·λ(f)                 from  λ(g) + Λ(a) ≥ λ(a) + α·λ(f)
    λ(f) ≥ (1 + α)·λ(a)                  from  λ(f) + α·λ(m) ≥ (1 + α)·λ(a) + α²·λ(m)
    α²·λ(g) ≤ Λ(f) + α·Λ(b)              from  Λ(f) + α·Λ(b) ≥ Λ(a) + α²·λ(g).

So α²·(1 + α + α²)·λ(a) ≤ α²·λ(g) ≤ Λ(f) + α·Λ(b) ≤ α·λ(a) + α³·λ(b) ≤ (α + α³)·λ(a), that
is (α⁴ + α² − α)·λ(a) ≤ 0, and a = 0.

*Second case, F·x ≠ ε·x.* Then F·F = ε²·I, and x̂ = F·x is not a multiple of x (a multiple
κ·x would have κ = ε, because y·F = ε·y). Multiplying
(5′) by F on the left gives ε²·B = α·x̂·(y·G), so B = (α/ε²)·x̂·(y·G). Then (4′) reads
(E·x̂)·(y·G) = x̂·(y·G·F). Here y·G ≠ 0, because B ≠ 0, and then y·G·F ≠ 0, because F is
invertible; so E·x̂ is a multiple of x̂. But
E·x̂ = ε′·x̂ + (ε − ε′)·(y·x̂)·x, so ε′ = ε and E = ε·I. Now (2′) reads
α·x̂·y = (α/ε)·x̂·(y·G), so y·G = ε·y and B = (α/ε)·x̂·y; and y·B = (α/ε)·(y·F·x)·y = α·y.
So y is a left eigenvector of all five matrices with eigenvalues α, α, ε, ε, ε, and (C)
applies. ∎

*Proof, right form, second statement.* If B ≠ A, this is (V′). If B = A, the argument for
the left form applies word for word, with the first statement for the right form. ∎

What Theorems 5, 6 and 8 leave open in dimension 2, in both forms, are the interpretations
in which the matrix of f is triangular or diagonal, Theorem 6 does not apply (f has a zero
on its diagonal, or neither t nor 2 mixes the coordinates), and the second statement of
Theorem 8 does not apply (all digit matrices are triangular in the same direction, or one
of the matrices of f, t, 0 is singular).

For the case in which no digit mixes the coordinates in one direction there is a reduction
to dimension 1.

**Lemma IV (dimension 2, both forms).** Suppose every digit matrix is upper triangular.
Then in an interpretation that makes every rule of T weakly decreasing and a strict rule
strictly decreasing, the first entry of the row r is positive, and the second entries of the
five digit vectors and of the vector of the other end marker are not all zero. The same
holds with the two coordinates exchanged when every digit matrix is lower triangular.

*Proof.* Because the digit matrices are upper triangular, the second coordinate of a product
M·v is the bottom right entry of M times the second coordinate of v. So the bottom right
entries of the digit matrices together with the second entries of the vectors satisfy every
weak condition of a one-dimensional interpretation. If the first entry of r is zero, every
condition for a strict rule only involves these numbers, with the second entry of r as the
multiplier of the top marker, and they form a one-dimensional interpretation with a strict
rule, against Theorem 4. If all the second entries of the vectors are zero, then the second
coordinate of the vector of every string is zero, the top left entries of the matrices and
the first entries of the vectors satisfy every condition by themselves, and with the first
entry of r as the multiplier of the top marker they form a one-dimensional interpretation
with a strict rule, again against Theorem 4. ∎

## 5. What the solver is asked

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

5. **Second pass.** The cases left undecided are taken up again with the results of
   sections 3 and 4. A pattern to which Theorem 6 or Theorem 8 applies is settled without
   the solver. For the others z3 is run again, with two changes. The conclusions of
   Lemma III (left form: g ≠ 0), of Lemma IV (triangular patterns) and of Corollary 10
   (irreducible digit matrices) are added as conditions. And a part that stays undecided is split by the size of the diagonal
   entries: each one that the pattern makes positive is either 1 or at least 2 (entries
   that Lemma I shows to be equal count once); a combination that still stays undecided
   is split once more on an entry off the diagonal.

`harness/dimension2.py --selftest` checks the encoding in two ways. The representation of the
value of a string given at the top of this note satisfies every weak condition, in both
forms, and its transpose does not, which tests the order of every product. And for two
smaller systems that do have a proof (T without `t▷ → 2▷` in the left form, T without the
left-end rules in the right form) the same procedure finds an interpretation that the checker
accepts; for the first of them also when the condition of Lemma III is added, as it must,
since the proof of the lemma does not use the rule that was dropped. Finally Theorems 5,
6 and 8 are tested on concrete digit matrices that satisfy their hypotheses and for which
the weak conditions can be met, among them one for each of the cases of Theorem 7 that the
proof of Theorem 8 has to treat: with the matrices fixed the remaining problem is small, z3
decides it, and it must find that no rule can be strict. And for digit matrices of each
of the two kinds that Corollary 10 allows, the weak conditions must remain satisfiable
when the condition of the corollary is added.

## 6. Results

The second pass for the right form is running; this section will be filled in when it
finishes.

## 7. Status

- Written proofs: Lemmas I to IV, Corollaries 1, 2 and 10, and Theorems 5 to 8. They have
  not been read by anyone else or checked by a proof assistant. The self-test of
  `harness/dimension2.py` and `harness/theorem7_check.py` test their statements on
  examples.
- The case analysis for the patterns that the theorems do not cover is not complete, so
  dimension 2 is not settled.
