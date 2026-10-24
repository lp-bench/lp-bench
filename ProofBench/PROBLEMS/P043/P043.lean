import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.MultiHypergraph

namespace FiniteMultiHypergraph

universe u

/-- The asymptotic assertion `t(μ,r) = e·μ·r·(1 + o_{μr}(1))`, along the
filter sending `(μ, r)` to infinity through the product `μ·r`. -/
def PaperTheorem24Asymptotic (t : ℝ → ℕ → ℕ) : Prop :=
  Filter.Tendsto
    (fun x : ℝ × ℕ =>
      ((t x.1 x.2 : ℝ) / (Real.exp 1 * x.1 * (x.2 : ℝ))) - 1)
    (Filter.comap (fun x : ℝ × ℕ => x.1 * (x.2 : ℝ)) Filter.atTop)
    (nhds (0 : ℝ))

/-- Theorem 2.4 of Planken–Ueckerdt, arXiv:2307.05757: there is a single
threshold function `t(μ, r) = e·μ·r·(1 + o_{μr}(1))` such that every
`r`-uniform `μ`-near-regular finite multihypergraph has a `t(μ, r)`-shallow
hitting edge set. -/
theorem P043 :
    ∃ t : ℝ → ℕ → ℕ,
      PaperTheorem24Asymptotic t ∧
        ∀ (W J : Type u) [DecidableEq W] [DecidableEq J]
          (μ : ℝ) (r : ℕ) (H : FiniteMultiHypergraph W J),
          0 < μ → 1 ≤ r → H.IsUniform r → H.IsNearRegular μ →
          H.HasShallowHittingEdgeSet (t μ r) := by
  sorry

end FiniteMultiHypergraph
