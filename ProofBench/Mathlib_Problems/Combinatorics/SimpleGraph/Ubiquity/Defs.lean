/-
Copyright (c) 2025 ProofBench participants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofBench participants
-/
module

public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Minor

/-!
# Ubiquitous graphs: definitions

The basic definitions of the Ubiquity project — `SimpleGraph.foldedUnion` and
`SimpleGraph.IsUbiquitous` — split out of the development in `Barbell.lean` so
that they can be imported on their own (in particular by the benchmark
problems `P022` and `P023` in `FINISHED`) without pulling in any proofs.
-/

@[expose] public section

variable {V W : Type*}

namespace SimpleGraph

/-! ### Ubiquitous graphs -/

/-- `α`-many copies of a simple graph `G`. -/
abbrev foldedUnion (G : SimpleGraph V) (α : Type*) : SimpleGraph (V × α) :=
  G.boxProd (.emptyGraph α)

/-- A graph `H` is ubiquitous if any graph `G` that contains arbitrarily many
disjoint copies of `H` as a minor also contains infinitely many disjoint
copies of `H` as a minor.

Note: We currently assume the graph has at most `Type`-many vertices, for simplicity. -/
def IsUbiquitous (H : SimpleGraph W) : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    (∀ n, (foldedUnion H (Fin n)).IsMinor G) → (foldedUnion H ℕ).IsMinor G

end SimpleGraph
