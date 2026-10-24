import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic

namespace ConvexSphereDiagram

variable {d n : ℕ}

/-- A convex body in `ℝ^d`: a compact convex set with nonempty interior.  Its boundary is a
tamely embedded `(d - 1)`-sphere. -/
def IsConvexBody (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- The strict zone with label `I`: the points on none of the boundaries that lie in exactly
the bodies `K j` with `j ∈ I`. -/
def zone (K : Fin n → Set (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j, x ∉ frontier (K j) ∧ (x ∈ K j ↔ j ∈ I)}

/-- Distinct boundaries share no patch: for `i ≠ j`, no nonempty relatively open subset of the
boundary of `K i` lies in the boundary of `K j`. -/
def NoSharedPatch (K : Fin n → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ i j, i ≠ j → ∀ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U →
    (U ∩ frontier (K i)).Nonempty → ¬ U ∩ frontier (K i) ⊆ frontier (K j)

/-- The zones with labels `I` and `insert i I` are adjacent across the boundary of `K i`: some
boundary point of `K i` lies on no other boundary and in exactly the other bodies indexed by
`I`.  For convex bodies without shared patches this is the same as the closures of the two
zones meeting along a relatively open patch of that boundary. -/
def Adjacent (K : Fin n → Set (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) (i : Fin n) :
    Prop :=
  ∃ p ∈ frontier (K i), ∀ j, j ≠ i → p ∉ frontier (K j) ∧ (p ∈ K j ↔ j ∈ I)

/-- The boundaries of `K` form a sphere diagram whose labelled region-adjacency graph is the full
cube `Q_n`: no shared patches, all `2 ^ n` zones nonempty and connected, and every two labels
that differ in one coordinate adjacent. -/
def RealizesFullCube (K : Fin n → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  NoSharedPatch K ∧ (∀ I, IsConnected (zone K I)) ∧ ∀ I i, i ∉ I → Adjacent K I i

/-- `Q_n` is the labelled region-adjacency graph of the boundaries of `n` convex bodies in
`ℝ^d`. -/
def ConvexCubeRealizable (d n : ℕ) : Prop :=
  ∃ K : Fin n → Set (EuclideanSpace ℝ (Fin d)), (∀ i, IsConvexBody (K i)) ∧ RealizesFullCube K

end ConvexSphereDiagram
