import ProofBench.PROBLEMS.P020.P020

/- ==============================================================================
P017 — Tutte's Wheel Theorem, contraction-sequence characterization.

The connectivity notion (`IsThreeConnected`, i.e. the shared library
`SimpleGraph.IsVertexConnected 3`) and the edge-contraction machinery
(`contractionRelation`, `contractionSetoid`, `ContractedV`,
`SimpleGraph.contractEdge`) are imported from `P020.lean`, so the two Tutte
formalizations share one set of definitions.
============================================================================== -/

open SimpleGraph

universe u

/-- A valid Tutte edge: both endpoints have degree ≥ 3. -/
structure ValidTutteContraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  edge : Sym2 V
  h_edge : edge ∈ G.edgeSet
  h_deg : ∀ v ∈ edge, G.degree v ≥ 3

/- Properly universe-polymorphic so that the base case `K₄` (which lives in
`Type 0`) and an arbitrary graph `G` (which lives in `Type u`) can coexist. -/
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

/- Tutte (1961): A graph G is 3-connected iff there exists a sequence
    G₀=K₄, G₁,…,Gₙ=G such that each Gᵢ = Gᵢ₊₁/xy with d(x), d(y) ≥ 3. -/
theorem P017 :
    IsThreeConnected G ↔ HasTutteSequence G := by
  constructor
  · sorry
  · sorry
