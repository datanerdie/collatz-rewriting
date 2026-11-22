# Phase 1 results

Produced by `harness/phase1.py`. The argument these checks support is in
`docs/phase1-shifted-system.md`.

## Rules

Every rule has one of the three allowed shapes; inner and left-end rules leave the
value of a string unchanged; dynamic rules apply exactly one step of the map. These
are exact identities between affine functions, not samples.

| System | Simulates | Symbols | Rules | Shape and arithmetic |
|---|---|---|---|---|
| T | the system T of the paper: n → n/2 or (3n+1)/2 | 7 | 11 | all hold |
| S | shifted system S: m → 3m/2 or (m+1)/2, one left marker, stops at 3 | 8 | 15 | all hold |
| S2 | shifted system S2: m → 3m/2 or (m+1)/2, two left markers, stops at 2 or 3 | 9 | 18 | all hold |
| T- | sibling of T for 3n−1: n → n/2 or (3n−1)/2 | 7 | 11 | all hold |
| S- | sibling of S for 3n−1, with m = n − 1: m → 3m/2 or (m−1)/2 | 7 | 11 | all hold |
| T5 | sibling of T for 5n+1: n → n/2 or (5n+1)/2 | 9 | 17 | all hold |

## Termination lemmas

One-dimensional natural interpretations on the reversed systems, verified by
`checker/check.py`. Certificates are next to this file.

| Statement | Rules | Checker |
|---|---|---|
| `S-without-left-end-rules-reversed` | 11 | accepted |
| `S-without-dynamic-rules-reversed` | 12 | accepted |
| `S2-without-left-end-rules-reversed` | 10 | accepted |
| `S2-without-dynamic-rules-reversed` | 16 | accepted |

## Exhaustive simulation

For each start string the complete rewrite graph was built: every rule at every
position of every reachable string. "Strings" counts graph nodes summed over all
start strings.

| System | Start strings | How many | Strings visited | Largest graph | Longest rewrite sequence | Result |
|---|---|---|---|---|---|---|
| T | binary strings of 1..1000 | 1,000 | 2,961,436 | 124,326 | 828 | follows the map, no cycle, stops only at a stop value |
| T | all canonical strings with up to 5 digits | 3,906 | 7,505,727 | 18,301 | 524 | follows the map, no cycle, stops only at a stop value |
| T | all strings of length 1..5 over the whole alphabet | 19,607 | 142,717 | 5,709 | 374 | no cycle |
| S | binary strings of 2..1000 | 999 | 3,330,401 | 143,655 | 889 | follows the map, no cycle, stops only at a stop value |
| S | all canonical strings with up to 5 digits | 9,331 | 15,411,580 | 19,906 | 572 | follows the map, no cycle, stops only at a stop value |
| S | all strings of length 1..5 over the whole alphabet | 37,448 | 205,226 | 6,544 | 412 | no cycle |
| S2 | binary strings of 2..1000 | 999 | 2,480,251 | 103,315 | 872 | follows the map, no cycle, stops only at a stop value |
| S2 | all canonical strings with up to 5 digits | 18,662 | 31,023,214 | 103,812 | 895 | follows the map, no cycle, stops only at a stop value |
| S2 | all strings of length 1..5 over the whole alphabet | 66,429 | 731,876 | 4,886 | 426 | no cycle |

## Long random runs

20 random 64-bit numbers per system, rules chosen uniformly at random among all
applicable ones until none applies. The number of dynamic steps must equal the number
of steps the map itself takes to reach a stop value.

| System | Runs | Dynamic steps (min–max) | Rewrite steps (min–max) | Result |
|---|---|---|---|---|
| T | 20 | 191–517 | 2,306–10,712 | all agree with the map |
| S | 20 | 210–470 | 2,906–10,654 | all agree with the map |
| S2 | 20 | 208–399 | 3,276–7,771 | all agree with the map |

## Siblings loop

Each sibling has a rewrite sequence that returns to its own start string, so it does
not terminate. The sequences were found by search and replayed step by step. Each
starts and ends at the binary string of the number in the "Start" column.

| System | Simulates | Start | Loop |
|---|---|---|---|
| T- | sibling of T for 3n−1: n → n/2 or (3n−1)/2 | 5 | ◁ft▷ → ◁f1▷ → ◁0t▷ → ◁01▷ → ◁t1▷ → ◁2f▷ → ◁2▷ → ◁ft▷ |
| T- | sibling of T for 3n−1: n → n/2 or (3n−1)/2 | 17 | ◁ffft▷ → ◁fff1▷ → ◁ff0t▷ → ◁ff01▷ → … (45 steps) … → ◁ffft▷ |
| S- | sibling of S for 3n−1, with m = n − 1: m → 3m/2 or (m−1)/2 | 4 | ◁ff▷ → ◁f0▷ → ◁0f▷ → ◁00▷ → ◁t0▷ → ◁1t▷ → ◁1▷ → ◁ff▷ |
| S- | sibling of S for 3n−1, with m = n − 1: m → 3m/2 or (m−1)/2 | 16 | ◁ffff▷ → ◁fff0▷ → ◁ff0f▷ → ◁ff00▷ → … (45 steps) … → ◁ffff▷ |
| T5 | sibling of T for 5n+1: n → n/2 or (5n+1)/2 | 13 | ◁tft▷ → ◁tf3₅▷ → ◁t1₅t▷ → ◁t1₅3₅▷ → … (21 steps) … → ◁tft▷ |
| T5 | sibling of T for 5n+1: n → n/2 or (5n+1)/2 | 17 | ◁ffft▷ → ◁fff3₅▷ → ◁ff1₅t▷ → ◁ff1₅3₅▷ → … (20 steps) … → ◁ffft▷ |
