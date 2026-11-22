# Phase 0 results

Each row is the Collatz system T with one rule left out. "Found" means the
published prover, driven by the python-sat build of CaDiCaL, found a proof with
the published search parameters. "Checker" is the verdict of `checker/check.py`
on the certificate saved next to this file.

| # | Rule left out | Type | Dimension | Coefficient values | Same problem as published | Found | Seconds | Steps | Checker |
|---|---|---|---|---|---|---|---|---|---|
| 1 | `f▷ → ▷` | natural | 3 | 4 | yes | yes | 3.7 | 1 | accepted |
| 2 | `t▷ → 2▷` | natural | 1 | 2 | yes | yes | 0.2 | 1 | accepted |
| 3 | `f0 → 0f` | natural | 4 | 2 | yes | yes | 0.5 | 3 | accepted |
| 4 | `f1 → 0t` | natural | 1 | 3 | yes | yes | 0.3 | 3 | accepted |
| 5 | `f2 → 1f` | natural | 1 | 2 | yes | yes | 0.3 | 2 | accepted |
| 6 | `t0 → 1t` | arctic | 3 | 4 | yes | yes | 1.0 | 3 | accepted |
| 7 | `t1 → 2f` | arctic | 4 | 3 | yes | yes | 0.6 | 3 | accepted |
| 8 | `t2 → 2t` | arctic | 2 | 5 | yes | yes | 0.4 | 3 | accepted |
| 9 | `◁0 → ◁t` | natural | 2 | 2 | yes | yes | 0.2 | 2 | accepted |
| 10 | `◁1 → ◁ff` | natural | 3 | 3 | yes | yes | 0.3 | 2 | accepted |
| 11 | `◁2 → ◁ft` | arctic | 4 | 3 | yes | yes | 4.0 | 2 | accepted |

Lemma 3.15 of the paper (hand-written interpretations, reversed systems):

| Statement | Rules | Checker |
|---|---|---|
| `lemma-3.15-T-without-left-end-rules-reversed` | 8 | accepted |
| `lemma-3.15-T-without-dynamic-rules-reversed` | 9 | accepted |
