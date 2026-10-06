import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Hypercube

open SimpleGraph Sensitivity

/-- **Antipodal edge-colourings of the hypercube** (Norine 2008; Open Problem Garden,
"Edge antipodal colorings of cubes").  Let `d ≥ 2` and two-colour the edges of the
`d`-dimensional hypercube `H d` so that antipodal edges — an edge and its image under
coordinatewise complementation — receive opposite colours.  Then some pair of antipodal
vertices is joined by a monochromatic path.  The colouring is an arbitrary map on unordered
pairs of vertices (only its values on edges matter); no properness is imposed, and a
monochromatic walk is asked for (a monochromatic path follows by removing repetitions). -/
theorem P079 : ∀ (d : ℕ), 2 ≤ d → ∀ c : Sym2 (Q d) → Bool, IsAntipodalColoring d c →
    ∃ (x : Q d) (w : (H d).Walk x (antipode x)) (b : Bool), IsMonochromatic c w b := by
  sorry
