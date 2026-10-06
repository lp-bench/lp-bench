import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Hypercube

open SimpleGraph Sensitivity

/-- Negation of `P079`: some antipodal two-colouring of the edges of a hypercube of dimension
at least `2` has no monochromatic walk between any pair of antipodal vertices. -/
theorem P079_disprove : ¬ (∀ (d : ℕ), 2 ≤ d → ∀ c : Sym2 (Q d) → Bool, IsAntipodalColoring d c →
    ∃ (x : Q d) (w : (H d).Walk x (antipode x)) (b : Bool), IsMonochromatic c w b) := by
  sorry
