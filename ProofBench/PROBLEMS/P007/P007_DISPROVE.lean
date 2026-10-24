import ProofBench.PROBLEMS.P007.P007

open MeasureTheory Metric Filter
open scoped ENNReal

/-- **Disprove version of P007.**  The negation of universal lattice optimality:
for some dimension `d`, the sphere-packing constant strictly exceeds the lattice
sphere-packing constant (no lattice packing is densest). -/
theorem P007_disprove :
    ¬ ∀ (d : ℕ), spherePackingConstant d = latticePackingConstant d := sorry
