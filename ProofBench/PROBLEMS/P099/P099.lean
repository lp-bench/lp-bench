import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Powerset

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

/-- The link of the face `f` in the complex spanned by `chambers`: the chambers containing
`f`, with `f` removed. -/
def link (chambers : Finset (Finset ℕ)) (f : Finset ℕ) : Finset (Finset ℕ) :=
  (chambers.filter fun t => f ⊆ t).image fun t => t \ f

/-- Combinatorial `d`-spheres, by recursion on `d`: a combinatorial `0`-sphere consists of
exactly two vertices; a combinatorial `(d+1)`-sphere is a family of `(d+1)`-simplices whose
realization is homeomorphic to `S^(d+1)` and all of whose vertex links are combinatorial
`d`-spheres. Hence every face link of a combinatorial sphere is again homeomorphic to a
sphere, which is what makes the dual cell complex a CW complex (the piecewise-linear
setting of the source); a triangulation that is merely homeomorphic to the sphere need
not have this property (double suspensions of homology spheres). -/
def IsCombinatorialSphere : ℕ → Finset (Finset ℕ) → Prop
  | 0, K => ∃ a b : ℕ, a ≠ b ∧ K = {{a}, {b}}
  | d + 1, K => (∀ t ∈ K, t.card = d + 2) ∧
      Nonempty (realization K ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 2))) 1) ∧
      ∀ v ∈ K.biUnion id, IsCombinatorialSphere d (link K {v})

/-- A (piecewise-linear) triangulation of `S^d`: a finite family of `d`-simplices, the
chambers, spanning a simplicial complex homeomorphic to the `d`-sphere in which every vertex
link is a combinatorial `(d-1)`-sphere, so that every face link is a sphere.
The `i`-cells are the faces of the
chambers with `i + 1` vertices, and the vertices are natural numbers, so that fresh ones
are always available for subdivisions. -/
structure Triangulation (d : ℕ) where
  chambers : Finset (Finset ℕ)
  card_chamber : ∀ t ∈ chambers, t.card = d + 1
  isSphere : Nonempty
    (realization chambers ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)
  /-- The piecewise-linear hypothesis of the source: every vertex link is a combinatorial
  `(d-1)`-sphere (for `d ≥ 1`; for `d = 0` the link is empty and the condition is void). -/
  link_sphere : ∀ v ∈ chambers.biUnion id, IsCombinatorialSphere (d - 1) (link chambers {v})

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

/-- Theorem 1 of Planken, arXiv:2409.11762: for `d ≥ 2` and a piecewise-linear
triangulation `C` of the `d`-sphere (every vertex link a combinatorial sphere, as the
dual cell complex argument of the source requires), the 1-skeleton of `C` is `(d+2)`-colourable
iff `C` is `Subdividable`; for
`d = 3` both are also equivalent to `MaximalSubdivisionBichromatic`. -/
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
