# Phase 3: cross-check of "ruled out" verdicts

Produced by `harness/crosscheck.py`. The search used the solver `cadical195` from the
python-sat package. Every 10th run that ended with "no interpretation of
this size removes any strict rule" (sorted by problem and configuration) was repeated
with the solver `glucose4` under a 120 second limit.

- Verdicts available for the sample: 3,022; sampled: 303.
- Sample by group: control 80, full 83, negative 60, target 80.
- Second solver agrees (also reports none exists): 303 (by dimension: 1: 120, 2: 113, 3: 70).
- Second solver undecided within the limit: 0.
- Second solver disagrees: 0.

Agreement is evidence against a solver bug, not against a bug in the encoding that
both solvers are given. A "ruled out" verdict is still not a certified result.
