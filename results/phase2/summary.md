# Phase 2 results

Produced by `harness/phase2.py`. The argument these checks support is in
`docs/phase2-block-acceleration.md`. `T.k3` is the paper's system T in blocks of 3
steps; `S.k3` is the shifted system S in blocks of 3 steps.

Every start value below 64 reaches 1 under the Collatz map (checked directly); the
equivalence argument for block size k needs this below 2^k.

## Block rules

"Arithmetic" means each block rule equals k steps of the map as an exact identity of
affine functions. "Derivable" means each block rule is a rewrite sequence of
single-step rules. "Shrinking blocks" counts the block rules that multiply by a
smaller power of 3 than the power of 2 they divide by.

| System | Block size | Symbols | Rules | Block rules | Shrinking blocks | Arithmetic | Derivable |
|---|---|---|---|---|---|---|---|
| T.k2 | 2 | 7 | 13 | 4 | 3 (75.0%) | all hold | all |
| S.k2 | 2 | 8 | 16 | 4 | 3 (75.0%) | all hold | all |
| T.k3 | 3 | 7 | 17 | 8 | 4 (50.0%) | all hold | all |
| S.k3 | 3 | 8 | 20 | 8 | 4 (50.0%) | all hold | all |
| T.k4 | 4 | 7 | 25 | 16 | 11 (68.8%) | all hold | all |
| S.k4 | 4 | 8 | 28 | 16 | 11 (68.8%) | all hold | all |
| T.k5 | 5 | 7 | 41 | 32 | 26 (81.2%) | all hold | all |
| S.k5 | 5 | 8 | 44 | 32 | 26 (81.2%) | all hold | all |
| T.k6 | 6 | 7 | 73 | 64 | 42 (65.6%) | all hold | all |
| S.k6 | 6 | 8 | 76 | 64 | 42 (65.6%) | all hold | all |

The block rules for the two smallest block sizes:

- **T.k2:** `ff▷ → ▷`, `ft▷ → 1▷`, `tf▷ → 2▷`, `tt▷ → 22▷`
- **S.k2:** `ff▷ → 00▷`, `ft▷ → s▷`, `tf▷ → 2▷`, `tt▷ → s0▷`
- **T.k3:** `fff▷ → ▷`, `fft▷ → 02▷`, `ftf▷ → 1▷`, `ftt▷ → 11▷`, `tff▷ → 2▷`, `tft▷ → 2▷`, `ttf▷ → 22▷`, `ttt▷ → 222▷`
- **S.k3:** `fff▷ → 000▷`, `fft▷ → s▷`, `ftf▷ → 10▷`, `ftt▷ → 2▷`, `tff▷ → 12▷`, `tft▷ → s0▷`, `ttf▷ → s0▷`, `ttt▷ → s00▷`

## Termination lemma

Each accelerated system without its left-end rules terminates: one-dimensional natural
interpretations on the reversed systems, verified by `checker/check.py`. (Without its
block rules an accelerated system is its base system without dynamic rules, covered
in Phases 0 and 1.)

| Statement | Rules | Checker |
|---|---|---|
| `T.k2-without-left-end-rules-reversed` | 10 | accepted |
| `S.k2-without-left-end-rules-reversed` | 12 | accepted |
| `T.k3-without-left-end-rules-reversed` | 14 | accepted |
| `S.k3-without-left-end-rules-reversed` | 16 | accepted |
| `T.k4-without-left-end-rules-reversed` | 22 | accepted |
| `S.k4-without-left-end-rules-reversed` | 24 | accepted |
| `T.k5-without-left-end-rules-reversed` | 38 | accepted |
| `S.k5-without-left-end-rules-reversed` | 40 | accepted |
| `T.k6-without-left-end-rules-reversed` | 70 | accepted |
| `S.k6-without-left-end-rules-reversed` | 72 | accepted |

## Exhaustive simulation

The complete rewrite graph from each start string: every rule at every position of
every reachable string. In the first two kinds of row, every block step must equal k
steps of the map, the graph must have no cycle, and rewriting may stop only at the
plain binary string of a value below 2^k.

| System | Start strings | How many | Strings visited | Largest graph | Longest rewrite sequence | Result |
|---|---|---|---|---|---|---|
| T.k2 | binary strings of 1..1000 | 1,000 | 1,483,213 | 64,308 | 745 | passed |
| T.k2 | all canonical strings with up to 5 digits | 3,906 | 3,768,545 | 8,738 | 453 | passed |
| T.k2 | all strings of length 1..4 over the whole alphabet | 2,800 | 6,177 | 46 | 26 | no cycle |
| S.k2 | binary strings of 2..1000 | 999 | 1,834,239 | 82,647 | 810 | passed |
| S.k2 | all canonical strings with up to 5 digits | 9,331 | 8,499,830 | 10,235 | 492 | passed |
| S.k2 | all strings of length 1..4 over the whole alphabet | 4,680 | 10,271 | 57 | 31 | no cycle |
| T.k3 | binary strings of 1..1000 | 1,000 | 985,061 | 45,337 | 691 | passed |
| T.k3 | all canonical strings with up to 5 digits | 3,906 | 2,522,408 | 6,518 | 407 | passed |
| T.k3 | all strings of length 1..4 over the whole alphabet | 2,800 | 5,854 | 29 | 22 | no cycle |
| S.k3 | binary strings of 2..1000 | 999 | 1,143,757 | 49,225 | 721 | passed |
| S.k3 | all canonical strings with up to 5 digits | 9,331 | 5,407,814 | 7,346 | 426 | passed |
| S.k3 | all strings of length 1..4 over the whole alphabet | 4,680 | 9,821 | 36 | 26 | no cycle |
| T.k4 | binary strings of 1..1000 | 1,000 | 740,192 | 35,247 | 655 | passed |
| T.k4 | all canonical strings with up to 5 digits | 3,906 | 1,886,993 | 3,842 | 372 | passed |
| T.k4 | all strings of length 1..4 over the whole alphabet | 2,800 | 5,733 | 13 | 9 | no cycle |
| S.k4 | binary strings of 2..1000 | 999 | 806,289 | 37,962 | 681 | passed |
| S.k4 | all canonical strings with up to 5 digits | 9,331 | 3,786,019 | 4,170 | 387 | passed |
| S.k4 | all strings of length 1..4 over the whole alphabet | 4,680 | 9,670 | 30 | 20 | no cycle |
| T.k5 | binary strings of 1..1000 | 1,000 | 575,618 | 31,045 | 624 | passed |
| T.k5 | all canonical strings with up to 5 digits | 3,906 | 1,452,845 | 4,077 | 337 | passed |
| T.k5 | all strings of length 1..4 over the whole alphabet | 2,800 | 5,728 | 13 | 9 | no cycle |
| S.k5 | binary strings of 2..1000 | 999 | 615,202 | 32,266 | 640 | passed |
| S.k5 | all canonical strings with up to 5 digits | 9,331 | 2,820,049 | 4,343 | 351 | passed |
| S.k5 | all strings of length 1..4 over the whole alphabet | 4,680 | 9,643 | 13 | 9 | no cycle |
| T.k6 | binary strings of 1..1000 | 1,000 | 415,442 | 24,256 | 580 | passed |
| T.k6 | all canonical strings with up to 5 digits | 3,906 | 985,743 | 3,453 | 320 | passed |
| T.k6 | all strings of length 1..4 over the whole alphabet | 2,800 | 5,728 | 13 | 9 | no cycle |
| S.k6 | binary strings of 2..1000 | 999 | 424,124 | 24,288 | 583 | passed |
| S.k6 | all canonical strings with up to 5 digits | 9,331 | 1,603,412 | 3,664 | 321 | passed |
| S.k6 | all strings of length 1..4 over the whole alphabet | 4,680 | 9,643 | 13 | 9 | no cycle |

## Long random runs

20 random 64-bit numbers per system, rules chosen uniformly at random among all
applicable ones until none applies. The number of block steps must equal the number
of k-step jumps the map itself needs to fall below 2^k.

| System | Runs | Block steps (min–max) | Rewrite steps (min–max) | Result |
|---|---|---|---|---|
| T.k2 | 20 | 87–196 | 2,251–7,681 | all agree with the map |
| S.k2 | 20 | 79–206 | 2,083–8,050 | all agree with the map |
| T.k3 | 20 | 59–136 | 1,972–7,365 | all agree with the map |
| S.k3 | 20 | 67–122 | 2,214–6,979 | all agree with the map |
| T.k4 | 20 | 59–110 | 3,857–7,983 | all agree with the map |
| S.k4 | 20 | 55–109 | 2,987–8,465 | all agree with the map |
| T.k5 | 20 | 35–78 | 2,686–6,773 | all agree with the map |
| S.k5 | 20 | 40–81 | 2,392–8,849 | all agree with the map |
| T.k6 | 20 | 32–85 | 3,149–9,949 | all agree with the map |
| S.k6 | 20 | 27–69 | 2,291–7,001 | all agree with the map |

## Accelerated siblings

An accelerated system stops as soon as a value below 2^k appears at a multiple of k
steps, so a cycle of the map survives acceleration only if it avoids such values.
For each sibling and block size the table gives a start value on a known cycle from
which the accelerated system has a loop (found by search and replayed), or "none" if
no member of the known cycles gives one.

| Sibling | k = 2 | k = 3 | k = 4 | k = 5 | k = 6 |
|---|---|---|---|---|---|
| T-: sibling of T for 3n−1: n → n/2 or (3n−1)/2 | loop from 5 (9 rewrite steps) | loop from 10 (4 rewrite steps) | loop from 17 (105 rewrite steps) | none | none |
| S-: sibling of S for 3n−1, with m = n − 1: m → 3m/2 or (m−1)/2 | loop from 4 (9 rewrite steps) | loop from 9 (4 rewrite steps) | loop from 16 (105 rewrite steps) | none | none |
| T5: sibling of T for 5n+1: n → n/2 or (5n+1)/2 | loop from 13 (32 rewrite steps) | loop from 13 (40 rewrite steps) | loop from 17 (41 rewrite steps) | none | none |
