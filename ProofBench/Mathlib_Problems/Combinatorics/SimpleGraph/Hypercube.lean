import Archive.Sensitivity
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

open SimpleGraph Sensitivity

/-- The hypercube graph on `Q n = Fin n → Bool`: two vertices are adjacent when they differ in
exactly one coordinate. -/
def H (n : ℕ) : SimpleGraph (Q n) :=
  {
  Adj := fun p q => ∃! i, p i ≠ q i
  symm := ⟨by intro _ _ hq; simpa only [ne_comm]⟩
  loopless := { irrefl := by intro a ; simp }
  }

/-- Coordinatewise complementation: the antipode of a vertex of the hypercube. -/
def antipode {n : ℕ} (p : Q n) : Q n := fun i => !p i

/-- The coordinates of the antipode. -/
@[simp] theorem antipode_apply {n : ℕ} (p : Q n) (i : Fin n) : antipode p i = !p i := rfl

/-- Taking the antipode twice gives back the vertex. -/
@[simp] theorem antipode_antipode {n : ℕ} (p : Q n) : antipode (antipode p) = p := by
  funext i; simp

/-- The antipode of a vertex differs from it in every coordinate. -/
theorem antipode_ne_apply {n : ℕ} (p : Q n) (i : Fin n) : antipode p i ≠ p i := by simp

/-- Complementation preserves adjacency, so it is an automorphism of the hypercube. -/
theorem adj_antipode {n : ℕ} {p q : Q n} (h : (H n).Adj p q) :
    (H n).Adj (antipode p) (antipode q) := by
  obtain ⟨i, hi, huniq⟩ := h
  refine ⟨i, by simpa using hi, fun j hj => huniq j (by simpa using hj)⟩

/-- A two-colouring of the edges of the hypercube (an arbitrary map on unordered pairs of
vertices; only its values on edges matter) is *antipodal* when antipodal edges, i.e. an edge
and its image under coordinatewise complementation, receive opposite colours. -/
def IsAntipodalColoring (n : ℕ) (c : Sym2 (Q n) → Bool) : Prop :=
  ∀ e ∈ (H n).edgeSet, c (e.map antipode) = !c e

/-- A walk in the hypercube is *monochromatic* of colour `b` when all its edges have colour
`b`. -/
def IsMonochromatic {n : ℕ} (c : Sym2 (Q n) → Bool) {x y : Q n} (w : (H n).Walk x y)
    (b : Bool) : Prop :=
  ∀ e ∈ w.edges, c e = b
