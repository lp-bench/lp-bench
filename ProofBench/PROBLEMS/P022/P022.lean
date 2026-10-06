/-
## Introduction
This file challenges you to prove that **every finite graph is ubiquitous**.

A graph `H` is *ubiquitous* if, whenever a graph `G` contains `n` pairwise
disjoint copies of `H` as a minor for every natural number `n`, then `G`
already contains infinitely many pairwise disjoint copies of `H` as a minor.

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

/-- **Finite graphs are ubiquitous.** -/
theorem P022 {W : Type*} [Finite W] (H : SimpleGraph W) : IsUbiquitous H := by
  sorry
