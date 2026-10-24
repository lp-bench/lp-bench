import Mathlib.Analysis.InnerProductSpace.PiL2
import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.Coloring

open Finset

namespace RangeCapturing

/-- Euclidean space `ℝ^d`; a point `x` has real coordinates `x 0, …, x (d-1)`. -/
abbrev Space (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- A range family in `ℝ^d`: any family of subsets of `ℝ^d`, for example all
axis-aligned strips. -/
abbrev RangeFamily (d : ℕ) : Type := Set (Set (Space d))

variable {d : ℕ}

/-- The `m`-uniform range-capturing hypergraph `H(V, R, m)` of Planken–Ueckerdt
(arXiv:2310.19982): vertex set `V`, and as hyperedges the `m`-element sets
`e ⊆ V` with `e = V ∩ ρ` for some range `ρ ∈ R`. -/
def rangeCapturingHypergraph (vertices : Finset (Space d)) (ranges : RangeFamily d)
    (m : ℕ) : FinHypergraph (Space d) :=
  let onV : FinHypergraph (Space d) := ⟨vertices, ∅, by simp⟩
  { vertices := vertices
    edges := { e | e.card = m ∧ ∃ range ∈ ranges, onV.CapturedBy e range }
    edges_subset_vertices := by
      rintro e ⟨-, range, -, hcap⟩
      exact FinHypergraph.capturedBy_subset hcap }

/-- Membership in the hyperedges of `H(V, R, m)`. -/
theorem mem_rangeCapturingHypergraph_edges {vertices edge : Finset (Space d)}
    {ranges : RangeFamily d} {m : ℕ} :
    edge ∈ (rangeCapturingHypergraph vertices ranges m).edges ↔
      edge.card = m ∧ ∃ range ∈ ranges,
        (rangeCapturingHypergraph vertices ranges m).CapturedBy edge range :=
  Iff.rfl

/-- A captured `m`-element set is a hyperedge of `H(V, R, m)`. -/
theorem mem_rangeCapturingHypergraph_edges_of_captured {vertices edge : Finset (Space d)}
    {ranges : RangeFamily d} {m : ℕ} {range : Set (Space d)}
    (hrange : range ∈ ranges)
    (hcap : (rangeCapturingHypergraph vertices ranges m).CapturedBy edge range)
    (hcard : edge.card = m) :
    edge ∈ (rangeCapturingHypergraph vertices ranges m).edges :=
  ⟨hcard, range, hrange, hcap⟩

/-- `H(V, R, m)` is `m`-uniform. -/
theorem rangeCapturingHypergraph_isUniform (vertices : Finset (Space d))
    (ranges : RangeFamily d) (m : ℕ) :
    (rangeCapturingHypergraph vertices ranges m).IsUniform m :=
  fun _ he => he.1

/-- `V` is in general position: distinct points of `V` differ in every
coordinate. As in Planken–Ueckerdt, the predicates below only quantify over point
sets in general position. -/
def GeneralPosition (vertices : Finset (Space d)) : Prop :=
  ∀ p ∈ vertices, ∀ q ∈ vertices, p ≠ q → ∀ i : Fin d, p i ≠ q i

/-- Subsets of a point set in general position are in general position. -/
theorem GeneralPosition.subset {V W : Finset (Space d)} (h : GeneralPosition V)
    (hWV : W ⊆ V) : GeneralPosition W :=
  fun p hp q hq hpq => h p (hWV hp) q (hWV hq) hpq

/-- Every `H(V, R, m)` with `V` in general position admits a polychromatic
`k`-coloring. -/
def PolychromaticBound (ranges : RangeFamily d) (k m : ℕ) : Prop :=
  ∀ vertices : Finset (Space d), GeneralPosition vertices →
    (rangeCapturingHypergraph vertices ranges m).IsPolychromaticColorable k

/-- The parameter `m_R(k)` (Definition 1 of Planken–Ueckerdt): the least `m` such
that every `H(V, R, m)` is polychromatically `k`-colorable, as an `sInf` (`0` if
there is no such `m`). -/
noncomputable def polychromaticParameter
  (ranges : RangeFamily d) (k : ℕ) : ℕ :=
  sInf { m | PolychromaticBound ranges k m }

/-- `R` admits uniform `t`-shallow hitting sets at uniformity `m`: every
`H(V, R, m)` with `V` in general position has a `t`-shallow hitting set. -/
def HasUniformShallowHittingSets (ranges : RangeFamily d) (m t : ℕ) : Prop :=
  ∀ vertices : Finset (Space d), GeneralPosition vertices → ∃ X : Finset (Space d),
    (rangeCapturingHypergraph vertices ranges m).ShallowHittingSet X t

/-- `R` is shrinkable: for `V` in general position and `m ≥ 1`, every hyperedge
of `H(V, R, m)` contains a hyperedge of `H(V, R, m-1)`. -/
def Shrinkable (ranges : RangeFamily d) : Prop :=
  ∀ (vertices : Finset (Space d)), GeneralPosition vertices →
    ∀ (m : ℕ), 1 ≤ m → ∀ (e : Finset (Space d)),
      e ∈ (rangeCapturingHypergraph vertices ranges m).edges →
        ∃ e' ∈ (rangeCapturingHypergraph vertices ranges (m - 1)).edges, e' ⊆ e

/-- `R_ST`: all axis-aligned strips `{x | a ≤ xᵢ ≤ b}` in `ℝ^d`, for a coordinate
`i` and reals `a, b`. -/
def stripFamily (d : ℕ) : RangeFamily d :=
  { R | ∃ (i : Fin d) (a b : ℝ), R = {x | a ≤ x i ∧ x i ≤ b} }

/-- `R_BL`: all bottomless rectangles `[a, b] × (-∞, c]` in `ℝ²`. -/
def bottomlessRectangles : RangeFamily 2 :=
  { R | ∃ a b c : ℝ, R = {x | a ≤ x 0 ∧ x 0 ≤ b ∧ x 1 ≤ c} }

/-- `R_TL`: all topless rectangles `[a, b] × [c, ∞)` in `ℝ²`. -/
def toplessRectangles : RangeFamily 2 :=
  { R | ∃ a b c : ℝ, R = {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1} }

/-- `R_UH`: all unit-height axis-aligned rectangles `[a, b] × [c, c+1]` in `ℝ²`. -/
def unitHeightRectangles : RangeFamily 2 :=
  { R | ∃ a b c : ℝ, R = {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ c + 1} }

end RangeCapturing
