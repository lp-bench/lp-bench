module

public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Minor

@[expose] public section

variable {V W : Type*}

namespace SimpleGraph

/-- The disjoint union of `α`-many copies of `G`: the box product of `G` with the
edgeless graph on `α`. -/
abbrev foldedUnion (G : SimpleGraph V) (α : Type*) : SimpleGraph (V × α) :=
  G.boxProd (.emptyGraph α)

/-- A graph `H` is ubiquitous if every graph `G` that contains `n` disjoint copies of `H`
as a minor for every `n` also contains infinitely many disjoint copies of `H` as a minor.
For simplicity the host graph's vertex type lies in `Type`. -/
def IsUbiquitous (H : SimpleGraph W) : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    (∀ n, (foldedUnion H (Fin n)).IsMinor G) → (foldedUnion H ℕ).IsMinor G

end SimpleGraph
