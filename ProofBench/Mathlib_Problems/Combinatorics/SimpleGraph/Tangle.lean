import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Three vertex sets cover `G` as induced subgraphs when they cover every
vertex—including isolated vertices—and every edge has both ends in one of
the sets.  This is Diestel's condition `G[A₀] ∪ G[A₁] ∪ G[A₂] = G`. -/
def SmallSidesCover (G : SimpleGraph V) (A : Fin 3 → Finset V) : Prop :=
  (∀ v, ∃ i, v ∈ A i) ∧
    ∀ ⦃u v⦄, G.Adj u v → ∃ i, u ∈ A i ∧ v ∈ A i

/-- A tangle of order `k` in the sense of Diestel: an orientation of every
separation of order below `k` such that the subgraphs induced by three
chosen small sides never cover the graph.  Repetitions among the three
separations are allowed. -/
structure Tangle (G : SimpleGraph V) (k : ℕ) where
  orientations : Set G.Separation
  lowOrder : ∀ ⦃s⦄, s ∈ orientations → s.order < k
  orients : ∀ s, s.order < k → (s ∈ orientations ↔ s.flip ∉ orientations)
  avoids : ∀ s : Fin 3 → G.Separation,
    (∀ i, s i ∈ orientations) →
      ¬G.SmallSidesCover fun i ↦ (s i).A

/-- A vertex set decides a tangle when every chosen separation points to
the side containing strictly more vertices of the set. -/
def Tangle.IsDecidedBy {G : SimpleGraph V} {k : ℕ} (τ : G.Tangle k)
    (X : Finset V) : Prop :=
  ∀ ⦃s⦄, s ∈ τ.orientations → (s.A ∩ X).card < (s.B ∩ X).card

end SimpleGraph
