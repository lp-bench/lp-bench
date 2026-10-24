import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Real.Basic

open SimpleGraph Matrix

/-- Restricted eigenvalues of a strongly regular graph: an eigenvalue `x` of the
adjacency matrix of an `srg(n, k, ℓ, μ)` with an eigenvector orthogonal to the
all-ones vector is a root of `x² + (μ - ℓ) x + (μ - k)` (Bose 1963). -/
theorem P090 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n k ℓ μ : ℕ} (hG : G.IsSRGWith n k ℓ μ) (x : ℝ) (v : V → ℝ) (hv : v ≠ 0)
    (hsum : ∑ i, v i = 0) (hx : G.adjMatrix ℝ *ᵥ v = x • v) :
    x ^ 2 + ((μ : ℝ) - ℓ) * x + ((μ : ℝ) - k) = 0 := by
  sorry
