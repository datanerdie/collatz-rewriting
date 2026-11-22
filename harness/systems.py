"""Rewriting systems that simulate Collatz-like maps, and problems derived from them.

Every symbol stands for a function on numbers, and a string is the composition of its symbols
applied from left to right.  The string `c a b d` is therefore d(b(a(c))) = 2*(2*1) + 1 = 5,
which is the binary numeral 1 0 1 read from the left.

    letter  paper   function         role
    a       f       x -> 2x          binary digit 0
    b       t       x -> 2x + 1      binary digit 1
    e       0       x -> 3x          ternary digit 0
    f       1       x -> 3x + 1      ternary digit 1
    g       2       x -> 3x + 2      ternary digit 2
    i       s       x -> x + 1       increment (shifted systems only)
    v..z    0..4    x -> 5x + 0..4   quinary digits (5n+1 system only)
    c       <|      the constant 1   left end marker
    p       <|2     the constant 2   left end marker (two-marker system only)
    q       <|3     the constant 3   left end marker (two-marker system only)
    d       |>      x -> x           right end marker

The letters a..g, c, d are the ones used in the files published with Yolcu, Aaronson & Heule,
"An Automated Approach to the Collatz Conjecture", so results can be compared line by line.
"""

# x -> A*x + B, stored as (A, B).  Left end markers are constants, so A = 0.
FUNCTION = {'a': (2, 0), 'b': (2, 1), 'e': (3, 0), 'f': (3, 1), 'g': (3, 2), 'i': (1, 1),
            'v': (5, 0), 'w': (5, 1), 'x': (5, 2), 'y': (5, 3), 'z': (5, 4),
            'c': (0, 1), 'p': (0, 2), 'q': (0, 3), 'd': (1, 0)}
PAPER = {'a': 'f', 'b': 't', 'e': '0', 'f': '1', 'g': '2', 'i': 's',
         'v': '0₅', 'w': '1₅', 'x': '2₅', 'y': '3₅', 'z': '4₅',
         'c': '◁', 'p': '◁₂', 'q': '◁₃', 'd': '▷'}
LEFT_MARKERS = 'cpq'
RIGHT_MARKER = 'd'
BINARY = 'ab'


def affine(string):
    """The function of a string, as (A, B) meaning x -> A*x + B."""
    A, B = 1, 0
    for s in string:
        a, b = FUNCTION[s]
        A, B = a * A, a * B + b
    return A, B


def value(string):
    """The number a canonical string (left marker, digits, right marker) stands for."""
    A, B = affine(string)
    assert A == 0, 'not a canonical string'
    return B


def pretty(string):
    return ''.join(PAPER[s] for s in string)


def pretty_rule(rule):
    return f'{pretty(rule[0])} → {pretty(rule[1])}'


class System:
    """A rewriting system together with the map on numbers it is meant to simulate.

    dynamic  rules `u d -> v d`: one step of the map, applied at the right end
    inner    rules without end markers: they must not change the value
    left     rules `m u -> m' v` at a left end marker: they must not change the value
    step     {0: (p, q), 1: (p, q)}: the map sends a value n of that parity to (p*n + q)/2
    stop     the values at which the simulated trajectory is finished
    """

    def __init__(self, name, title, dynamic, inner, left, step, stop):
        self.name, self.title = name, title
        self.dynamic, self.inner, self.left = list(dynamic), list(inner), list(left)
        self.step, self.stop = step, frozenset(stop)

    @property
    def rules(self):
        return self.dynamic + self.inner + self.left

    @property
    def auxiliary(self):
        return self.inner + self.left

    @property
    def symbols(self):
        return sorted({s for l, r in self.rules for s in l + r})

    @property
    def digits(self):
        return [s for s in self.symbols if s not in LEFT_MARKERS and s != RIGHT_MARKER]

    @property
    def markers(self):
        return [s for s in self.symbols if s in LEFT_MARKERS]

    def apply_map(self, n):
        p, q = self.step[n % 2]
        assert (p * n + q) % 2 == 0
        return (p * n + q) // 2

    def encode(self, n):
        """The canonical binary string for n."""
        bits = bin(n)[2:]
        if self.markers == ['c']:
            head, rest = 'c', bits[1:]
        else:                                   # two markers: the leading bits 10 or 11
            assert n >= 2
            head, rest = {'10': 'p', '11': 'q'}[bits[:2]], bits[2:]
        return head + rest.replace('0', 'a').replace('1', 'b') + RIGHT_MARKER

    def problem(self, strict, top=False):
        """A problem file: the rules in `strict` are strict, all others weak."""
        arrow = '|->' if top else '->'
        return ''.join(f'{l} {arrow if (l, r) in strict else "->="} {r}\n'
                       for l, r in self.rules)


# ---------------------------------------------------------------------------------------
# The system T of the paper:  n -> n/2  or  (3n+1)/2, stopping at 1.
# ---------------------------------------------------------------------------------------
DYNAMIC = [('ad', 'd'),     # f|> -> |>     n even:  n -> n/2
           ('bd', 'gd')]    # t|> -> 2|>    n odd:   n -> (3n+1)/2
# Move a ternary digit one place to the left without changing the value.
CARRY = [('ae', 'ea'), ('af', 'eb'), ('ag', 'fa'),
         ('be', 'fb'), ('bf', 'ga'), ('bg', 'gb')]
# Absorb a ternary digit at the left end.
LEFT = [('ce', 'cb'), ('cf', 'caa'), ('cg', 'cab')]

T = DYNAMIC + CARRY + LEFT          # the 11 rules, in the paper's order

COLLATZ = System(
    'T', 'the system T of the paper: n → n/2 or (3n+1)/2',
    DYNAMIC, CARRY, LEFT, step={0: (1, 0), 1: (3, 1)}, stop={1})

# ---------------------------------------------------------------------------------------
# Shifted systems.  With m = n + 1 the Collatz map becomes
#     U(m) = 3m/2      (m even)
#     U(m) = (m+1)/2   (m odd)
# on m >= 2, with the single cycle 2 -> 3 -> 2 if the conjecture is true.
# ---------------------------------------------------------------------------------------
# Move an increment one place to the left:  2x + 1 = (2x) + 1  and  2(x+1) = (2x+1) + 1.
INCREMENT = [('ai', 'b'), ('bi', 'ia')]

# S: one left marker, stops at 3.  The even step is the bare relabelling f|> -> 0|>; the odd
# step looks at one more digit so that it cannot fire on the string for 3.
SHIFTED = System(
    'S', 'shifted system S: m → 3m/2 or (m+1)/2, one left marker, stops at 3',
    dynamic=[('ad', 'ed'),      # f|>  -> 0|>     2x      -> 3x
             ('abd', 'bd'),     # ft|> -> t|>     4x + 1  -> 2x + 1
             ('bbd', 'iad')],   # tt|> -> sf|>    4x + 3  -> 2x + 2 = 2(x + 1)
    inner=CARRY + INCREMENT,
    left=LEFT + [('ci', 'ca')],                     # 1 + 1 = 2
    step={0: (3, 0), 1: (1, 1)}, stop={3})

# S2: two left markers standing for 2 and 3, so neither dynamic rule needs a context.
SHIFTED_TWO_MARKERS = System(
    'S2', 'shifted system S2: m → 3m/2 or (m+1)/2, two left markers, stops at 2 or 3',
    dynamic=[('ad', 'ed'),      # f|> -> 0|>      2x      -> 3x
             ('bd', 'id')],     # t|> -> s|>      2x + 1  -> x + 1
    inner=CARRY + INCREMENT,
    left=[('pe', 'qa'), ('pf', 'qb'), ('pg', 'paa'),        # 6, 7, 8
          ('qe', 'pab'), ('qf', 'pba'), ('qg', 'pbb'),      # 9, 10, 11
          ('pi', 'q'), ('qi', 'pa')],                       # 3, 4
    step={0: (3, 0), 1: (1, 1)}, stop={2, 3})

# ---------------------------------------------------------------------------------------
# Siblings with extra cycles.  None of these may ever be reported as terminating.
# ---------------------------------------------------------------------------------------
# 3n-1 in the paper's style: n -> n/2 or (3n-1)/2.  Cycles through 5 and through 17.
THREE_N_MINUS_ONE = System(
    'T-', 'sibling of T for 3n−1: n → n/2 or (3n−1)/2',
    dynamic=[('ad', 'd'), ('bd', 'fd')],            # t|> -> 1|>:  2x + 1 -> 3x + 1
    inner=CARRY, left=LEFT, step={0: (1, 0), 1: (3, -1)}, stop={1})

# 3n-1 shifted by m = n - 1:  m -> 3m/2 or (m-1)/2.  It differs from the shifted Collatz
# systems only in rounding the odd case down instead of up, so no increment is needed.
SHIFTED_THREE_N_MINUS_ONE = System(
    'S-', 'sibling of S for 3n−1, with m = n − 1: m → 3m/2 or (m−1)/2',
    dynamic=[('ad', 'ed'), ('bd', 'd')],            # t|> -> |>:   2x + 1 -> x
    inner=CARRY, left=LEFT, step={0: (3, 0), 1: (1, -1)}, stop={1})

# 5n+1 in the paper's style, in mixed binary and quinary.  Cycles through 13 and through 17.
# There is no shifted form: (5n+1)/2 has the fixed point -1/3, which is not an integer.
_QUINARY = 'vwxyz'
FIVE_N_PLUS_ONE = System(
    'T5', 'sibling of T for 5n+1: n → n/2 or (5n+1)/2',
    dynamic=[('ad', 'd'), ('bd', 'yd')],            # t|> -> 3_5|>:  2x + 1 -> 5x + 3
    # binary digit b then quinary digit k:  5(2x + b) + k = 2(5x + k') + b'
    inner=[(BINARY[b] + _QUINARY[k], _QUINARY[(5 * b + k) // 2] + BINARY[(5 * b + k) % 2])
           for b in range(2) for k in range(5)],
    left=[('cv', 'cab'), ('cw', 'cba'), ('cx', 'cbb'), ('cy', 'caaa'), ('cz', 'caab')],
    step={0: (1, 0), 1: (5, 1)}, stop={1})

SYSTEMS = [COLLATZ, SHIFTED, SHIFTED_TWO_MARKERS,
           THREE_N_MINUS_ONE, SHIFTED_THREE_N_MINUS_ONE, FIVE_N_PLUS_ONE]


# ---------------------------------------------------------------------------------------
# Problems used in Phase 0
# ---------------------------------------------------------------------------------------

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
