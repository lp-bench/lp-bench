# LPBench: research-level combinatorics in Lean 4

[Website](https://lp-bench.github.io) ·
**Problems** (this repository) ·
[Evaluation harness](https://github.com/lp-bench/QEDRank) ·
[Apptainer sandbox](https://github.com/lp-bench/QEDRank/tree/main/inspectAI-apptainer)

LPBench (formerly ProofBench) is a benchmark of **117 research-level problems**, most of them in
combinatorics and graph theory, stated in Lean 4 with Mathlib. Each problem is a
single theorem whose proof is `sorry`; a solution replaces it with a proof that
Lean accepts. The problems are taken from the research literature and from open
conjectures, and are curated by mathematicians at TU Bergakademie Freiberg
and Universität Hamburg.

| Category    | Problems | What it means                                          |
|-------------|---------:|--------------------------------------------------------|
| Open        | 32       | open conjectures: prove the statement or its negation  |
| Literature  | 64       | results with a published proof                         |
| Calibration | 21       | elementary or textbook results, to check an evaluation |

By Mathematics Subject Classification, 83 problems are in graph theory (05C), 8
in designs, configurations and matroids (05B) and 6 in extremal combinatorics
(05D); the other 20 range over other parts of combinatorics, number theory,
discrete and convex geometry, group theory, linear algebra, topology,
probability, order theory, set theory and theoretical computer science. Browse them on the [website](https://lp-bench.github.io/problems.html)
or in [`Database.json`](ProofBench/DATABASE/Database.json).

## An example

Problem P112 is the matroid intersection conjecture for *tame* matroids, in
which every circuit meets every cocircuit in a finite set. The conjecture for
arbitrary infinite matroids was refuted in October 2026, by matroids that are
not tame; the tame case is open.

```lean
-- ProofBench/Mathlib_Problems/Combinatorics/Matroid/Intersection.lean
def Tame (M : Matroid α) : Prop :=
  ∀ ⦃C K : Set α⦄, M.IsCircuit C → M.IsCocircuit K → (C ∩ K).Finite

def SatisfiesIntersection (M N : Matroid α) : Prop :=
  ∃ J₀ J₁ : Set α, Disjoint J₀ J₁ ∧ M.Indep (J₀ ∪ J₁) ∧ N.Indep (J₀ ∪ J₁) ∧
    M.closure J₀ ∪ N.closure J₁ = M.E

-- ProofBench/PROBLEMS/P112/P112.lean
theorem P112 {α : Type*} (M N : Matroid α) (hE : M.E = N.E) (hM : M.Tame) (hN : N.Tame) :
    M.SatisfiesIntersection N := by
  sorry
```

Because P112 is open, `P112_DISPROVE.lean` next to it states the negation.
Proving either of the two solves the problem, so the files do not reveal which
answer we expect.

## Getting started

You need Lean 4 through [elan](https://lean-lang.org/install/). Then:

```bash
git clone https://github.com/lp-bench/lp-bench
cd lp-bench
lake exe cache get                          # download compiled Mathlib (a few minutes)
lake build ProofBench.PROBLEMS.P112.P112    # check that a problem file builds
```

The first build also compiles Peter Nelson's
[Matroid](https://github.com/apnelson1/Matroid) library, which some statements
use. Versions: Lean 4.34.1, Mathlib v4.34.1, and Matroid from the branch
[`proofbench-v4.34.1`](https://github.com/utkuokur/Matroid/tree/proofbench-v4.34.1)
of a fork, which adapts the library to that Mathlib release.

To attempt a problem, open its file, replace the `sorry` and build it again. Two
files contain more than one `sorry` (P017, P070); every one of them must be
replaced.

## What counts as a solution

- The theorem statement and every definition in the problem file stay unchanged.
- Imports are limited to Mathlib, the statement library
  `ProofBench.Mathlib_Problems`, the Matroid library and your own files.
- No `sorry`, no new axioms and no `native_decide`; the proof may depend only
  on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.
- The proof passes [Comparator](https://github.com/leanprover/comparator), the
  Lean FRO's adversarial proof checker, which replays it through the Lean
  kernel.

The [evaluation harness](https://github.com/lp-bench/QEDRank)
implements exactly these checks. A claimed solution of an open problem is also
checked by hand.

## What is in this repository

```
ProofBench/PROBLEMS/Pxxx/Pxxx.lean            the problem: one theorem, proof replaced by sorry
ProofBench/PROBLEMS/Pxxx/Pxxx_DISPROVE.lean   its negation (open problems only)
ProofBench/Mathlib_Problems/                  definitions needed to state the problems
                                              but missing from Mathlib (53 modules)
ProofBench/DATABASE/Database.json             per problem: id, name, category, MSC class,
                                              informal statement (LaTeX), summary, Lean statement
```

## How the statements were checked

A Lean statement can easily say something other than what was intended. We
therefore check each problem with a **theorem sandwich**: a stronger statement,
or a set of key lemmas, that implies the problem, and easy corollaries that
follow from it, each with a Lean proof of the implication. A statement that is
accidentally too strong makes the upper bound unprovable; one that is too weak
fails to give the corollaries. The sandwiches and our reference proofs are kept
private, so that they do not give away solutions.

## Problems resolved or corrected since they were added

Four problems were open when they were added and were resolved in OpenAI's
October 2026 release of mathematical results
([github.com/openai/math](https://github.com/openai/math)): Hadwiger's,
Sidorenko's and Ryser's conjectures (P001, P004, P008) were refuted, and
Seymour's second neighbourhood conjecture (P027) was proved. P001, P004 and
P008 now ask for the refutation. In October 2026 the Erdős–Hajnal conjecture
for paths (P005) was proved by Nguyen ([arXiv:2610.24887](https://arxiv.org/abs/2610.24887)),
and Google DeepMind released a Lean formalization of a proof found by its
Cogentic system; P005 is now a literature problem. The solutions of all five
are public, so results on them measure reproduction rather than discovery.

P099, Planken's theorem on colouring the 1-skeleton of triangulations, was
corrected on 6 November 2026 after three evaluated models objected that its
statement was false: the formal statement now carries the piecewise-linear
hypothesis that the source takes for granted. The problem keeps its number;
the earlier statement is in the history of this repository.

## Evaluating AI systems

The [evaluation harness](https://github.com/lp-bench/QEDRank)
runs AI agents on these problems under identical conditions (the same agent
loop, tools, budgets and sandbox for every model) and grades their proofs with
Lean and Comparator. It works on a PC with Docker and on HPC clusters with
Apptainer.

The first ten problems are the full forms of
[Ten Challenges](https://tenchallenges.github.io/ten-challenges/), our public
challenge of ten parameterized open problems in combinatorics, where anyone can
submit a proof for any value of the parameter and have it checked
automatically.

## Reporting a problem

If a statement does not say what it should, or a definition looks wrong,
please [open an issue](https://github.com/lp-bench/lp-bench/issues).

## For maintainers

This repository is exported from the LPBench development repository, which
also holds the theorem sandwiches and reference proofs; edit problems there,
not here. To regenerate:

    scripts/sync_from_proofbench.py ../proofbench-hidden --build   # path to the development repository
    git add -A && git commit -m "Sync LPBench $(cut -c1-10 SOURCE_COMMIT)"

The script exports the last commit of LPBench, not uncommitted changes. It
stops if a statement imports hidden material, and skips (and reports) a library
file that does.
