# collatz-rewriting

Experiments on the Collatz conjecture as a termination problem for string rewriting, building
on Yolcu, Aaronson & Heule, [*An Automated Approach to the Collatz Conjecture*](https://doi.org/10.1007/s10817-022-09658-8)
(Journal of Automated Reasoning, 2023; [arXiv:2105.14697](https://arxiv.org/abs/2105.14697)).

**This repository does not contain a proof of the Collatz conjecture, and the expected outcome
of the work is a negative or partial result.** Its purpose is to test, reproducibly, whether
two reformulations of the paper's rewriting system make the open step any easier for automated
search.

## Background

The paper encodes a number in mixed binary and ternary and gives an 11-rule rewriting system
*T* that terminates on every string if and only if the Collatz conjecture is true. It also shows
that *T* with any one rule left out can be proved terminating automatically, by matrix
interpretations found with a SAT solver. What is missing is a single interpretation that
decreases strictly on one rule of *T* and weakly on the other ten.

## The question

Does either of these changes enlarge what small matrix interpretations can prove?

1. **Shift by one.** With *m = n + 1* the Collatz map becomes "even *m* → 3*m*/2, odd *m* →
   (*m* + 1)/2", so the growth step is a relabelling of one digit and the "+1" moves into a
   separate carry.
2. **Block acceleration.** Replace the two single-step rules by 2^k rules that apply *k* steps
   at once, so that an interpretation only has to decrease across a whole block.

The paper's own hybrid system (its Section 3.3) already uses an increment symbol, so the first
idea is a variation on existing work, not a new one. It is included as a comparison.

## Plan

| Phase | Work | Status |
|---|---|---|
| 0 | Reproduce the 11 published "one rule left out" proofs; check them with an independent checker | done: all 11 found and accepted, see `results/phase0/summary.md` |
| 1 | Fix the shifted system and prove "terminates ⇔ Collatz" for it; build correct 3n−1 and 5n+1 siblings | done: proof in `docs/phase1-shifted-system.md`, checks in `results/phase1/summary.md` |
| 2 | Generate block-accelerated systems for block sizes 2–6 and test them against direct iteration | done: argument in `docs/phase2-block-acceleration.md`, checks in `results/phase2/summary.md` |
| 3 | Search: original, shifted, accelerated and combined systems, across interpretation type, dimension and coefficient range; record proved / ruled out / timed out. Includes the residue-class statements modulo 8 that the paper leaves open | in progress: design in `docs/phase3-search.md`, results so far in `results/phase3/` |
| 4 | Write up what the grid shows | not started |

Controls in Phase 3: the paper's solvable variants must stay solvable in the new encodings
(otherwise the encoding is worse and that branch stops), and the 3n−1 and 5n+1 systems, which
have extra cycles, must never be reported as terminating. Phase 2 showed that this second
control is available only for the single-step systems and for block sizes up to 4: with larger
blocks the accelerated siblings no longer have a known loop. Any claimed proof for the full system
is treated as a bug until it passes the independent checker and a second prover.

## Layout

| Path | What it is |
|---|---|
| `checker/check.py` | Independent checker for natural and arctic matrix-interpretation certificates. Exact integer arithmetic, no code shared with any prover. |
| `tests/test_checker.py` | Tests for the checker, including corrupted certificates that must be rejected. |
| `harness/systems.py` | Our own definitions of the paper's system *T*, the shifted systems, the 3n−1 and 5n+1 siblings, and the problems derived from them. |
| `harness/run_published.py` | Runs the published prover on one problem and saves its interpretations as a JSON certificate. |
| `harness/cadical` | Stand-in for the `cadical` command line used by the published prover, backed by the `python-sat` package. |
| `harness/phase0.py` | Runs Phase 0 end to end. |
| `harness/rewrite.py` | Small rewriting engine: all successors of a string, full rewrite graphs, cycle detection. |
| `harness/checks.py` | The checks shared by Phases 1 and 2: rule arithmetic, termination lemmas, exhaustive simulation, random runs, loop search. |
| `harness/phase1.py` | Runs the Phase 1 checks on the shifted systems and the siblings. |
| `harness/phase2.py` | Builds the block-accelerated systems for block sizes 2–6 and runs the same checks on them. |
| `docs/phase1-shifted-system.md` | Definition of the shifted systems S and S2 and the proof that each terminates exactly when the Collatz conjecture holds. |
| `harness/phase3.py` | The search: builds every problem, runs the prover over a grid with time limits, verifies every proof, writes the summary. Resumable. |
| `docs/phase3-search.md` | What is searched for, why a proof would mean what is claimed, and how to read the results. |
| `docs/phase2-block-acceleration.md` | Definition of the block-accelerated systems, the same equivalence for them, and what acceleration does to the negative controls. |
| `scripts/fetch_baseline.sh` | Fetches the code published with the paper at a pinned commit into `third_party/` (not committed: it has no licence file). |
| `problems/`, `results/` | Problem files and the certificates and summaries produced for them. |

## Running

```bash
python3 -m venv .venv && .venv/bin/pip install -r requirements.txt
```

```bash
./scripts/fetch_baseline.sh
```

```bash
.venv/bin/python tests/test_checker.py
```

```bash
.venv/bin/python harness/phase0.py
```

```bash
python3 harness/phase1.py
```

```bash
python3 harness/phase2.py
```

```bash
.venv/bin/python harness/phase3.py --validate --run control target full negative --report
```

To check a single certificate:

```bash
python3 checker/check.py problems/phase0/collatz-T-06.srs results/phase0/collatz-T-06.json
```

## What a Phase 0 certificate does and does not show

Each `collatz-T-NN` certificate is a machine-checked proof that the left-end rules of *T* (with
rule *NN* left out) can be used only finitely often when applied at the left end of a string.
Termination of *T* without rule *NN* then follows from three results of the paper: Lemma 3.15
(checked here, see the `lemma-3.15-*` certificates), and Lemmas 3.16 and 3.18, which are
pen-and-paper arguments that this repository does not machine-check.
