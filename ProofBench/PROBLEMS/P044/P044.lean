import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.RotationSystem
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

open SimpleGraph

universe u

/-- **Whitney's uniqueness theorem** (1932): a 3-connected planar graph has a
unique combinatorial embedding up to reflection — any two planar rotation
systems coincide, or coincide after reversing all rotations. -/
theorem P044 {V : Type u} [Finite V] {G : SimpleGraph V}
    (h3 : G.IsVertexConnected 3) {R₁ R₂ : G.RotationSystem}
    (h₁ : R₁.IsPlanar) (h₂ : R₂.IsPlanar) :
    R₂ = R₁ ∨ R₂ = R₁.reflect := by
  sorry
