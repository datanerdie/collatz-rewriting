# Phase 3 results

Produced by `harness/phase3.py --report`. Every run is listed in `runs.jsonl` next to
this file; `certificates/` holds every complete proof and the partial proofs for the
target and full problems.

- "proved" means the published prover found a complete proof and `checker/check.py`
  accepted it. The smallest configuration that succeeded is shown.
- "ruled out" counts configurations for which the SAT solver reported that no
  interpretation of that type, dimension and coefficient range exists. These verdicts
  come from the solver alone and are not independently certified.
- "timed out" counts configurations that reached the time limit undecided. A timeout
  says nothing either way.
- "left" and "right" are the two search forms: left-end rules strict at the left end,
  or dynamic rules strict at the right end. A proof in either form is a proof.

1,589 prover runs are recorded, with time limits of 120 seconds and dimensions 1 to 3.

## Controls: statements the paper proved

Every non-convergent Collatz trajectory visits the given residue class. For block encodings (`T.k`, `S.k`) the statement proved is stronger: the
class is visited at a step count that is a multiple of the block size.

### Visits 1 mod 4

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c2 | 11 | no proof: 25 ruled out, 5 timed out | **proved**: natural, dimension 2, 4 values, 0 s |
| S.c2 | 15 | no proof: 26 ruled out, 4 timed out; best partial removes 1 strict rule(s), leaves 3 | **proved**: natural, dimension 2, 4 values, 0 s |
| T.k2 | 12 | no proof: 25 ruled out, 5 timed out | no proof: 25 ruled out, 5 timed out |
| S.k2 | 15 | no proof: 26 ruled out, 4 timed out | no proof: 25 ruled out, 5 timed out |

### Visits 3 mod 4

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c2 | 11 | **proved**: natural, dimension 2, 4 values, 0 s | **proved**: natural, dimension 2, 11 values, 1 s |
| S.c2 | 15 | **proved**: arctic, dimension 2, 6 values, 1 s | **proved**: natural, dimension 2, 11 values, 1 s |
| T.k2 | 12 | **proved**: natural, dimension 2, 3 values, 0 s | **proved**: natural, dimension 1, 11 values, 0 s |
| S.k2 | 15 | **proved**: natural, dimension 3, 4 values, 30 s | **proved**: natural, dimension 1, 11 values, 0 s |

### Visits 3 mod 8

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c3 | 13 | no proof: 25 ruled out, 5 timed out | **proved**: arctic, dimension 3, 6 values, 10 s |
| S.c3 | 17 | no proof: 26 ruled out, 4 timed out; best partial removes 1 strict rule(s), leaves 3 | **proved**: natural, dimension 3, 11 values, 21 s |
| T.k3 | 16 | no proof: 26 ruled out, 4 timed out | no proof: 26 ruled out, 4 timed out |
| S.k3 | 19 | no proof: 27 ruled out, 3 timed out | no proof: 25 ruled out, 5 timed out |

### Visits 1 or 5 mod 8

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c3 | 12 | no proof: 26 ruled out, 4 timed out | **proved**: natural, dimension 2, 4 values, 1 s |
| S.c3 | 16 | no proof: 26 ruled out, 4 timed out; best partial removes 1 strict rule(s), leaves 3 | **proved**: natural, dimension 2, 4 values, 0 s |
| T.k3 | 15 | no proof: 26 ruled out, 4 timed out | no proof: 26 ruled out, 4 timed out |
| S.k3 | 18 | no proof: 27 ruled out, 3 timed out | no proof: 25 ruled out, 5 timed out |

### Visits 1 or 7 mod 8

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c3 | 12 | **proved**: arctic, dimension 2, 6 values, 1 s | **proved**: natural, dimension 3, 8 values, 6 s |
| S.c3 | 16 | **proved**: arctic, dimension 3, 6 values, 17 s | no proof: 25 ruled out, 5 timed out |
| T.k3 | 15 | no proof: 25 ruled out, 5 timed out | no proof: 25 ruled out, 5 timed out |
| S.k3 | 18 | no proof: 26 ruled out, 4 timed out | no proof: 25 ruled out, 5 timed out |

## Targets: statements the paper leaves open

Every non-convergent Collatz trajectory visits the given residue class. For block encodings (`T.k`, `S.k`) the statement proved is stronger: the
class is visited at a step count that is a multiple of the block size.

### Visits 1 mod 8

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c3 | 13 | no proof: 26 ruled out, 4 timed out | no proof: 26 ruled out, 4 timed out |
| S.c3 | 17 | no proof: 26 ruled out, 4 timed out | no proof: 26 ruled out, 4 timed out |
| T.k3 | 16 | no proof: 26 ruled out, 4 timed out | no proof: 26 ruled out, 4 timed out |
| S.k3 | 19 | no proof: 27 ruled out, 3 timed out | no proof: 24 ruled out, 6 timed out |

### Visits 5 mod 8

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c3 | 13 | no proof: 25 ruled out, 5 timed out | no proof: 26 ruled out, 4 timed out |
| S.c3 | 17 | no proof: 26 ruled out, 4 timed out | no proof: 26 ruled out, 4 timed out; best partial removes 1 strict rule(s), leaves 4 |
| T.k3 | 16 | no proof: 26 ruled out, 4 timed out | no proof: 26 ruled out, 4 timed out |
| S.k3 | 19 | no proof: 27 ruled out, 3 timed out | no proof: 24 ruled out, 5 timed out |

### Visits 7 mod 8

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c3 | 13 | no proof: 25 ruled out, 2 timed out | no proof: 25 ruled out, 1 timed out |
| S.c3 | 17 | no proof: 25 ruled out, 1 timed out; best partial removes 1 strict rule(s), leaves 3 | not run |
| T.k3 | 16 | not run | not run |
| S.k3 | 19 | not run | not run |

### Visits 5 or 7 mod 8

| Encoding | Rules | Left form | Right form |
|---|---|---|---|
| T.c3 | 12 | not run | not run |
| S.c3 | 16 | not run | not run |
| T.k3 | 15 | not run | not run |
| S.k3 | 18 | not run | not run |

## The Collatz conjecture itself

Each system terminates if and only if the conjecture is true.

| System | Rules | Left form | Right form |
|---|---|---|---|
| T | 11 | not run | not run |
| S | 15 | not run | not run |
| S2 | 18 | not run | not run |
| T.c2 | 12 | not run | not run |
| S.c2 | 16 | not run | not run |
| T.c3 | 14 | not run | not run |
| S.c3 | 18 | not run | not run |
| T.k2 | 13 | not run | not run |
| S.k2 | 16 | not run | not run |
| T.k3 | 17 | not run | not run |
| S.k3 | 20 | not run | not run |
| T.k4 | 25 | not run | not run |
| S.k4 | 28 | not run | not run |
| T.k5 | 41 | not run | not run |
| S.k5 | 44 | not run | not run |
| T.k6 | 73 | not run | not run |
| S.k6 | 76 | not run | not run |

## Negative controls: systems that loop

Each of these has an explicit loop, so "proved" in this table would be a bug. Partial removals are legitimate: a looping system can still have rules that are used only finitely often.

| System | Rules | Left form | Right form |
|---|---|---|---|
| T- | 11 | not run | not run |
| S- | 11 | not run | not run |
| T5 | 17 | not run | not run |
| T-.k2 | 13 | not run | not run |
| S-.k2 | 13 | not run | not run |
| T5.k2 | 19 | not run | not run |
| T-.k3 | 17 | not run | not run |
| S-.k3 | 17 | not run | not run |
| T5.k3 | 23 | not run | not run |
| T-.k4 | 25 | not run | not run |
| S-.k4 | 25 | not run | not run |
| T5.k4 | 31 | not run | not run |

## Integrity

- Proofs reported for looping systems: 0.
- Certificates rejected by the checker: 0.
- Runs that ended in an error instead of a verdict: 0.
