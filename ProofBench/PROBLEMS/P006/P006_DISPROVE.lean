import ProofBench.PROBLEMS.P006.P006

/-- **Disprove version of P006**: for some ordinal `r`, finite planar graphs (`r` even)
or all finite graphs (`r` odd) are not `(r / 2)`-well-quasi-ordered under minors. -/
theorem P006_disprove :
    ¬ ∀ r,
      if r % 2 = 0
      then IsAlphaWQO PlanarGraph.MinorLE (r / 2)
      else IsAlphaWQO FiniteGraph.MinorLE (r / 2) := by
  sorry
