import ProofBench.Mathlib_Problems.Geometry.ConvexSphereDiagram

open ConvexSphereDiagram

/-- Negation of `P026`: in some dimension `d ≥ 4`, some cube `Q_n` is not the labelled
region-adjacency graph of the boundaries of `n` convex bodies. -/
theorem P026_disprove : ¬ ∀ d : ℕ, 4 ≤ d → ∀ n : ℕ, ConvexCubeRealizable d n := by
  sorry
