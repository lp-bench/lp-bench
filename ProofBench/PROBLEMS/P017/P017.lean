import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Contraction

open SimpleGraph

universe u

/-- A valid Tutte edge of `G`: an edge both of whose endpoints have degree at least `3`. -/
structure ValidTutteContraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  edge : Sym2 V
  h_edge : edge ∈ G.edgeSet
  h_deg : ∀ v ∈ edge, G.degree v ≥ 3

/-- `G` has a Tutte sequence: `G` is isomorphic to `K₄`, or contracting some valid Tutte edge of
`G` gives a graph isomorphic to one with a Tutte sequence. -/
inductive HasTutteSequence : {V : Type u} → [Fintype V] → [DecidableEq V] →
    (G : SimpleGraph V) → [DecidableRel G.Adj] → Prop
  | base {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (h_iso : G ≃g completeGraph (Fin 4)) :
      HasTutteSequence G
  | step {V W : Type u} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
      {G_next : SimpleGraph V} [DecidableRel G_next.Adj]
      {G_prev : SimpleGraph W} [DecidableRel G_prev.Adj]
      (h_prev : HasTutteSequence G_prev)
      (c : ValidTutteContraction G_next)
      (h_iso : G_prev ≃g G_next.contractEdge c.edge) :
      HasTutteSequence G_next

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Tutte's characterisation of 3-connected graphs (Tutte 1961): `G` is 3-connected iff there is
a sequence `G₀ = K₄, G₁, …, Gₙ = G` with each `Gᵢ = Gᵢ₊₁ / xy` for an edge `xy` of `Gᵢ₊₁` whose
endpoints have degree at least `3`. -/
theorem P017 :
    IsThreeConnected G ↔ HasTutteSequence G := by
  constructor
  · sorry
  · sorry
