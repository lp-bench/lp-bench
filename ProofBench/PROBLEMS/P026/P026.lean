import ProofBench.Mathlib_Problems.Geometry.ConvexSphereDiagram

open ConvexSphereDiagram

/-- **Full cube adjacency by convex bodies.**  For every `d ≥ 4` and every `n`, the cube `Q_n` is
the labelled region-adjacency graph of the boundaries of `n` convex bodies in `ℝ^d`.  Tame
spheres realise every `Q_n` when `d ≥ 4`; for convex bodies only `n ≤ ⌊3d/2⌋` is known. -/
theorem P026 : ∀ d : ℕ, 4 ≤ d → ∀ n : ℕ, ConvexCubeRealizable d n := by
  sorry
