import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Metric Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d)))

/- The definition of a *sphere packing* `C ⊆ ℝ^d`. -/
def IsSpherePacking : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → 2 ≤ dist x y

/-- The (upper) density of a packing `C`. -/
def upperDensity : ℝ≥0∞ :=
  limsup (fun R : ℝ =>
    volume ((⋃ x ∈ C, ball x 1) ∩ ball 0 R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) atTop

/- The **sphere-packing constant** `Δ_d`: the supremum of densities over all unit
packings of `ℝ^d`. -/
def spherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ (C : Set (EuclideanSpace ℝ (Fin d))) (_ : IsSpherePacking C), upperDensity C

/- A *lattice packing*: a unit packing whose centre set is an additive subgroup
of `ℝ^d` (a lattice). -/
def IsLatticePacking : Prop :=
  IsSpherePacking C ∧
    ∃ L : AddSubgroup (EuclideanSpace ℝ (Fin d)), C = (L : Set (EuclideanSpace ℝ (Fin d)))

/- The **lattice** sphere-packing constant:
the supremum of densities over unit packings that are lattices. -/
def latticePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ (C : Set (EuclideanSpace ℝ (Fin d))) (_ : IsLatticePacking C),
    upperDensity C

/-! ### Unconditional facts: densities are fractions, and dimension `0` -/

/-! ### Local finiteness of packings -/
