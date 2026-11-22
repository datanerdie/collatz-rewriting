"""The Collatz rewriting system T of Yolcu, Aaronson & Heule, and problems derived from it.

Strings are read as compositions of functions, leftmost symbol outermost, so the string
`c a b d` stands for the number t(f(1)) = 5 written in binary as 1 0 1.

    letter  paper   meaning
    a       f       x -> 2x          (binary digit 0)
    b       t       x -> 2x + 1      (binary digit 1)
    c       <|      the constant 1   (left end marker)
    d       |>      x -> x           (right end marker)
    e       0       x -> 3x          (ternary digit 0)
    f       1       x -> 3x + 1      (ternary digit 1)
    g       2       x -> 3x + 2      (ternary digit 2)

The letters are the ones used in the files published with the paper, so results can be
compared line by line.
"""

# Dynamic rules: one step of the Collatz map T(n) = n/2 or (3n+1)/2 at the right end.
DYNAMIC = [('ad', 'd'),     # f|> -> |>     n even:  n -> n/2
           ('bd', 'gd')]    # t|> -> 2|>    n odd:   n -> (3n+1)/2
# Auxiliary rules: move a ternary digit one place to the left without changing the value.
CARRY = [('ae', 'ea'), ('af', 'eb'), ('ag', 'fa'),
         ('be', 'fb'), ('bf', 'ga'), ('bg', 'gb')]
# Auxiliary rules: absorb a ternary digit at the left end.
LEFT = [('ce', 'cb'), ('cf', 'caa'), ('cg', 'cab')]

T = DYNAMIC + CARRY + LEFT          # the 11 rules, in the paper's order


def subsystem_problem(k):
    """Problem k (1..11): T with rule k left out.

    The left-end rules that remain are strict and restricted to the left end (`|->`); every
    other remaining rule is weak (`->=`).  Solving it shows that the left-end rules can be
    used only finitely often, which with Lemmas 3.15, 3.16 and 3.18 of the paper gives
    termination of T without rule k.
    """
    lines = []
    for i, (l, r) in enumerate(T, 1):
        if i == k:
            continue
        lines.append(f'{l} {"|->" if (l, r) in LEFT else "->="} {r}')
    return '\n'.join(lines) + '\n'


def reversed_strict(rules):
    """All rules strict, every string reversed (termination is invariant under reversal)."""
    return ''.join(f'{l[::-1]} -> {r[::-1]}\n' for l, r in rules)
