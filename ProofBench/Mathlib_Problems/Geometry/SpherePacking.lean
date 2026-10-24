import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Metric Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ} (C : Set (EuclideanSpace ℝ (Fin d)))

/-- `C ⊆ ℝ^d` is the set of centres of a packing of unit balls: distinct centres are at
distance at least `2`. -/
def IsSpherePacking : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → 2 ≤ dist x y

/-- The upper density of `C`: the `limsup` as `R → ∞` of the proportion of the ball of
radius `R` about the origin covered by the unit balls centred at the points of `C`. -/
def upperDensity : ℝ≥0∞ :=
  limsup (fun R : ℝ =>
    volume ((⋃ x ∈ C, ball x 1) ∩ ball 0 R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) atTop

/-- The sphere-packing constant `Δ_d`: the supremum of the upper densities of all unit
ball packings of `ℝ^d`. -/
def spherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ (C : Set (EuclideanSpace ℝ (Fin d))) (_ : IsSpherePacking C), upperDensity C

/-- A lattice packing: a unit ball packing whose set of centres is an additive subgroup
of `ℝ^d`. -/
def IsLatticePacking : Prop :=
  IsSpherePacking C ∧
    ∃ L : AddSubgroup (EuclideanSpace ℝ (Fin d)), C = (L : Set (EuclideanSpace ℝ (Fin d)))

/-- The lattice sphere-packing constant: the supremum of the upper densities of all
lattice packings of `ℝ^d`. -/
def latticePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ (C : Set (EuclideanSpace ℝ (Fin d))) (_ : IsLatticePacking C),
    upperDensity C
