import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Hypercube

open SimpleGraph Sensitivity

/-- **Antipodal edge-colourings of the hypercube** (Norine 2008, Open Problem Garden): for
`d ≥ 2`, every antipodal two-colouring of the edges of the hypercube `H d` admits a
monochromatic walk from some vertex to its antipode.  The colouring is an arbitrary map on
unordered pairs of vertices; only its values on edges matter. -/
theorem P079 : ∀ (d : ℕ), 2 ≤ d → ∀ c : Sym2 (Q d) → Bool, IsAntipodalColoring d c →
    ∃ (x : Q d) (w : (H d).Walk x (antipode x)) (b : Bool), IsMonochromatic c w b := by
  sorry
