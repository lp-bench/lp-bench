/-
## Introduction
This file challenges you to prove that **Andreae's ubiquity conjecture fails
for locally finite graphs**: there exists a locally finite (countable) graph
that is not ubiquitous.  Local finiteness is encoded as the hypothesis
`∀ v, (H.neighborSet v).Finite` (every vertex has a finite neighbourhood).

A graph `H` is *ubiquitous* if, whenever a graph `G` contains `n` pairwise
disjoint copies of `H` as a minor for every natural number `n`, then `G`
already contains infinitely many pairwise disjoint copies of `H` as a minor.
By `P022` (finite graphs are ubiquitous) any non-ubiquitous graph must be
infinite, so countability is the first interesting regime.

The definitions are imported from `ProofBench.Mathlib.Combinatorics.SimpleGraph.Ubiquity.Defs`:

* `foldedUnion H α` (`= H □ emptyGraph α`) is the disjoint union of `α`-many
  copies of `H`;
* `IsUbiquitous H` says: for every graph `G` (on a `Type`-small vertex set),
  if `foldedUnion H (Fin n)` is a minor of `G` for every `n`, then
  `foldedUnion H ℕ` is a minor of `G`.

The minor relation `SimpleGraph.IsMinor` comes from
`ProofBench.Mathlib.Combinatorics.SimpleGraph.Minor`.
-/

import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Ubiquity.Defs

open SimpleGraph

/- Do not modify above this line. -/

/-- **There is a locally finite (countable) graph that is not ubiquitous.**

This refutes Andreae's ubiquity conjecture, which is stated for locally finite
graphs.  The hypothesis `∀ v, (H.neighborSet v).Finite` is what separates a
genuine refutation from the strictly weaker claim that some merely *countable*
graph fails ubiquity. -/
theorem P023 :
    ∃ (W : Type) (_ : Countable W) (H : SimpleGraph W),
      (∀ v, (H.neighborSet v).Finite) ∧ ¬ IsUbiquitous H := by
  sorry
