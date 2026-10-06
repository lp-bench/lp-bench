import Mathlib.Analysis.InnerProductSpace.PiL2
import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.Coloring

open Finset

namespace RangeCapturing

/- =====================================================================
The geometry: `ℝ^d`, range families, and the range capturing hypergraph
`H(V, R, m)` as an honest `Hypergraph` object.
===================================================================== -/

/- Euclidean `d`-space `ℝ^d` (`EuclideanSpace ℝ (Fin d)`, definitionally
`Fin d → ℝ`): a point `x` has real coordinates `x 0, x 1, …, x (d-1)`. -/
abbrev Space (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/- A **range family** in `ℝ^d` is a family of subsets of `ℝ^d` (paper, §1):
for example all axis-aligned strips, all halfplanes, or all unit balls. -/
abbrev RangeFamily (d : ℕ) : Type := Set (Set (Space d))

variable {d : ℕ}

/- The **`m`-uniform range capturing hypergraph** `H(V, R, m)` (paper, §1 and
Definition 1): vertex set `V`, its hyperedges the `m`-element subsets of `V`
captured by some range of the family `R` (`Hypergraph.CapturedBy`, i.e.
`edge = V ∩ range`).  Capture is phrased directly via `CapturedBy`, against the
carrier `onV : Hypergraph` whose vertex set is `V` — `CapturedBy` only ever reads
`.vertices`, so its (empty) edge set is immaterial, and `onV.vertices` is
definitionally the resulting `H.vertices`. -/
def rangeCapturingHypergraph (vertices : Finset (Space d)) (ranges : RangeFamily d)
    (m : ℕ) : Hypergraph (Space d) :=
  let onV : Hypergraph (Space d) := ⟨vertices, ∅, by simp⟩
  { vertices := vertices
    edges := { e | e.card = m ∧ ∃ range ∈ ranges, onV.CapturedBy e range }
    edges_subset_vertices := by
      rintro e ⟨-, range, -, hcap⟩
      exact Hypergraph.capturedBy_subset hcap }

theorem mem_rangeCapturingHypergraph_edges {vertices edge : Finset (Space d)}
    {ranges : RangeFamily d} {m : ℕ} :
    edge ∈ (rangeCapturingHypergraph vertices ranges m).edges ↔
      edge.card = m ∧ ∃ range ∈ ranges,
        (rangeCapturingHypergraph vertices ranges m).CapturedBy edge range :=
  Iff.rfl

/- A convenient constructor for hyperedges of `H(V, R, m)`. -/
theorem mem_rangeCapturingHypergraph_edges_of_captured {vertices edge : Finset (Space d)}
    {ranges : RangeFamily d} {m : ℕ} {range : Set (Space d)}
    (hrange : range ∈ ranges)
    (hcap : (rangeCapturingHypergraph vertices ranges m).CapturedBy edge range)
    (hcard : edge.card = m) :
    edge ∈ (rangeCapturingHypergraph vertices ranges m).edges :=
  ⟨hcard, range, hrange, hcap⟩

/- `H(V, R, m)` is indeed `m`-uniform. -/
theorem rangeCapturingHypergraph_isUniform (vertices : Finset (Space d))
    (ranges : RangeFamily d) (m : ℕ) :
    (rangeCapturingHypergraph vertices ranges m).IsUniform m :=
  fun _ he => he.1

/- **General position** (paper, §1): the points of `V` have pairwise distinct
coordinates.  The paper assumes it throughout; the three predicates below are
stated for point sets in general position (added 2026-09-08 — without it
`Shrinkable` fails for the four corners of the unit square). -/
def GeneralPosition (vertices : Finset (Space d)) : Prop :=
  ∀ p ∈ vertices, ∀ q ∈ vertices, p ≠ q → ∀ i : Fin d, p i ≠ q i

theorem GeneralPosition.subset {V W : Finset (Space d)} (h : GeneralPosition V)
    (hWV : W ⊆ V) : GeneralPosition W :=
  fun p hp q hq hpq => h p (hWV hp) q (hWV hq) hpq

/- `PolychromaticBound R k m`: every `H(V, R, m)` admits a polychromatic
`k`-coloring; i.e. uniformity `m` already suffices for `k` colors. -/
def PolychromaticBound (ranges : RangeFamily d) (k m : ℕ) : Prop :=
  ∀ vertices : Finset (Space d), GeneralPosition vertices →
    (rangeCapturingHypergraph vertices ranges m).IsPolychromaticColorable k

/- The paper's **`m_R(k)`** (Definition 1): the least uniformity `m` at which
every `H(V, R, m)` is polychromatically `k`-colorable.
Phrasing it as an `sInf` lets `m_R(k) ≤ M` be
discharged by exhibiting `PolychromaticBound R k M`. -/
noncomputable def polychromaticParameter
  (ranges : RangeFamily d) (k : ℕ) : ℕ :=
  sInf { m | PolychromaticBound ranges k m }

/- `R` admits uniform `t`-shallow hitting sets at uniformity `m`: every
hypergraph `H(V, R, m)` has some `t`-shallow hitting set. -/
def HasUniformShallowHittingSets (ranges : RangeFamily d) (m t : ℕ) : Prop :=
  ∀ vertices : Finset (Space d), GeneralPosition vertices → ∃ X : Finset (Space d),
    (rangeCapturingHypergraph vertices ranges m).ShallowHittingSet X t

/- A range family is **shrinkable** (paper, §1.2): every hyperedge of `H(V,R,m)`
contains a hyperedge of `H(V,R,m-1)`. -/
def Shrinkable (ranges : RangeFamily d) : Prop :=
  ∀ (vertices : Finset (Space d)), GeneralPosition vertices →
    ∀ (m : ℕ), 1 ≤ m → ∀ (e : Finset (Space d)),
      e ∈ (rangeCapturingHypergraph vertices ranges m).edges →
        ∃ e' ∈ (rangeCapturingHypergraph vertices ranges (m - 1)).edges, e' ⊆ e

/- =====================================================================
The four geometric range families of the paper, defined explicitly as
families of subsets of `ℝ^d`/`ℝ²`.  General position — pairwise distinct
coordinates, assumed throughout the paper — is `GeneralPosition` above.
===================================================================== -/

/- `R_ST`: all **axis-aligned strips** in `ℝ^d` — for a coordinate `i` and reals
`a, b`, the slab `{x | a ≤ xᵢ ≤ b}`. -/
def stripFamily (d : ℕ) : RangeFamily d :=
  { R | ∃ (i : Fin d) (a b : ℝ), R = {x | a ≤ x i ∧ x i ≤ b} }

/- `R_BL`: all **bottomless rectangles** `[a,b] × (-∞, c]` in `ℝ²`. -/
def bottomlessRectangles : RangeFamily 2 :=
  { R | ∃ a b c : ℝ, R = {x | a ≤ x 0 ∧ x 0 ≤ b ∧ x 1 ≤ c} }

/- `R_TL`: all **topless rectangles** `[a,b] × [c, ∞)` in `ℝ²`. -/
def toplessRectangles : RangeFamily 2 :=
  { R | ∃ a b c : ℝ, R = {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1} }

/- `R_UH`: all **unit-height axis-aligned rectangles** `[a,b] × [c, c+1]` in `ℝ²`. -/
def unitHeightRectangles : RangeFamily 2 :=
  { R | ∃ a b c : ℝ, R = {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ c + 1} }

end RangeCapturing
