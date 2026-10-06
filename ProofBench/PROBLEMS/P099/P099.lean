import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Powerset

/- ---------------------------------------------------------------- -/
/- Paper: COLOURING THE 1-SKELETON OF d-DIMENSIONAL TRIANGULATIONS -/
/- ---------------------------------------------------------------- -/

namespace TriangulationColouring

/-- The faces with exactly `n` vertices of the simplicial complex spanned by `chambers`;
these are its `(n-1)`-cells. -/
def faces (chambers : Finset (Finset ℕ)) (n : ℕ) : Finset (Finset ℕ) :=
  chambers.biUnion fun t => t.powersetCard n

/-- The `(n-1)`-cells incident with the cell `f`. -/
def facesAt (chambers : Finset (Finset ℕ)) (n : ℕ) (f : Finset ℕ) : Finset (Finset ℕ) :=
  (faces chambers n).filter fun g => f ⊆ g

/-- The geometric realization, in barycentric coordinates, of the simplicial complex
spanned by `chambers`: the union of the closed simplices on the chambers. -/
def realization (chambers : Finset (Finset ℕ)) : Set (ℕ → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ ∃ t ∈ chambers, (∀ v, x v ≠ 0 → v ∈ t) ∧ ∑ v ∈ t, x v = 1}

/-- A triangulation of `S^d`: a finite family of `d`-simplices, the chambers, spanning a
simplicial complex homeomorphic to the `d`-sphere. The `i`-cells are the faces of the
chambers with `i + 1` vertices, and the vertices are natural numbers, so that fresh ones
are always available for subdivisions. -/
structure Triangulation (d : ℕ) where
  chambers : Finset (Finset ℕ)
  card_chamber : ∀ t ∈ chambers, t.card = d + 1
  isSphere : Nonempty
    (realization chambers ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)

namespace Triangulation

variable {d : ℕ}

/-- The 1-skeleton of a triangulation: two vertices are adjacent when they span a 1-cell,
that is, when they lie in a common chamber. -/
def skeleton (C : Triangulation d) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ ∃ t ∈ C.chambers, u ∈ t ∧ v ∈ t
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ ht => ⟨ht.1, ht.2.2, ht.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Subdividing a chamber `t` at a new vertex `v`: the chamber is replaced by the `d + 1`
chambers spanned by `v` together with a `(d-1)`-cell of `t`. -/
def subdivideChamber (t : Finset ℕ) (v : ℕ) : Finset (Finset ℕ) :=
  t.image fun u => insert v (t.erase u)

/-- `K'` arises from `K` by subdividing every chamber of `T`, the new vertices being
pairwise distinct and unused by `K`. -/
def IsSubdivisionOn (K T K' : Finset (Finset ℕ)) : Prop :=
  T ⊆ K ∧ ∃ v : Finset ℕ → ℕ, Set.InjOn v T ∧ (∀ t ∈ T, ∀ s ∈ K, v t ∉ s) ∧
    K' = (K \ T) ∪ T.biUnion fun t => subdivideChamber t (v t)

/-- `C'` is a subdivision of `C`: it arises from `C` by subdividing a set of chambers. -/
def IsSubdivision (C C' : Triangulation d) : Prop :=
  ∃ T, IsSubdivisionOn C.chambers T C'.chambers

/-- Assertion (2) of Theorem 1: `C` has a subdivision in which every `(d-2)`-cell is
incident with a number of `(d-1)`-cells divisible by three. -/
def Subdividable (C : Triangulation d) : Prop :=
  ∃ C' : Triangulation d, IsSubdivision C C' ∧
    ∀ f ∈ faces C'.chambers (d - 1), 3 ∣ (facesAt C'.chambers d f).card

/-- Assertion (3) of Theorem 1, stated for `d = 3`: the maximal subdivision of `C`, the
one subdividing every chamber, has a 2-edge-colouring in which no 2-cell is
monochromatic. -/
def MaximalSubdivisionBichromatic (C : Triangulation d) : Prop :=
  ∀ K', IsSubdivisionOn C.chambers C.chambers K' →
    ∃ c : Finset ℕ → Bool, ∀ f ∈ faces K' 3,
      ∃ e₁ ∈ f.powersetCard 2, ∃ e₂ ∈ f.powersetCard 2, c e₁ ≠ c e₂

end Triangulation

end TriangulationColouring

open TriangulationColouring TriangulationColouring.Triangulation

/-- **Theorem 1 (Planken).** Let `d ≥ 2` and let `C` be a triangulation of the `d`-sphere.
The 1-skeleton of `C` has a proper `(d+2)`-colouring if and only if `C` has a subdivision
in which the number of `(d-1)`-cells incident with any `(d-2)`-cell is divisible by three.
Moreover, for `d = 3` both are equivalent to the maximal subdivision of `C` having a
2-edge-colouring without monochromatic 2-cells. -/
theorem P099 (d : ℕ) (_hd : 2 ≤ d) (C : Triangulation d) :
    (C.skeleton.Colorable (d + 2) ↔ C.Subdividable) ∧
      (d = 3 → (C.skeleton.Colorable (d + 2) ↔ C.MaximalSubdivisionBichromatic)) := by
  sorry

/-- Direct corollary: a triangulation whose 1-skeleton contains a clique on `d + 3`
vertices has no subdivision all of whose `(d-2)`-cells are incident with a number of
`(d-1)`-cells divisible by three. -/
theorem P099_no_subdivision_of_clique (d : ℕ) (hd : 2 ≤ d) (C : Triangulation d)
    (s : Finset ℕ) (hcard : d + 3 ≤ s.card) (hclique : C.skeleton.IsClique s) :
    ¬ C.Subdividable := fun hsub => by
  have := hclique.card_le_of_colorable ((P099 d hd C).1.mpr hsub)
  omega
