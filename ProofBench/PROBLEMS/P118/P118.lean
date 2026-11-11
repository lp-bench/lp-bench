import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

namespace CornerLemma

open Finset

/-- A vertex of the cube `{0,1}³`. -/
abbrev Vertex := Fin 3 → Bool

/-- A face of the cube: every coordinate is fixed to a value or left free (`none`). The faces
without a free coordinate are the vertices, and `fun _ => none` is the cube itself. -/
abbrev Face := Fin 3 → Option Bool

/-- The dimension of a face: its number of free coordinates. -/
def dim (f : Face) : ℕ := (univ.filter fun i => f i = none).card

/-- The vertex `v` lies in the face `f`: it agrees with `f` on every fixed coordinate. -/
abbrev InFace (v : Vertex) (f : Face) : Prop := ∀ i, f i = none ∨ f i = some (v i)

/-- Two vertices are adjacent in the cube when they differ in exactly one coordinate. -/
abbrev Adj (u w : Vertex) : Prop := (univ.filter fun i => u i ≠ w i).card = 1

/-- The value of the cut between a vertex set `A` and its complement under the face weighting
`lam`: the total weight of the faces that contain both endvertices of an edge of the cut. -/
def cutValue (lam : Face → ℕ) (A : Finset Vertex) : ℕ :=
  ∑ f ∈ univ.filter (fun f : Face => ∃ u w, Adj u w ∧ u ∈ A ∧ w ∉ A ∧ InFace u f ∧ InFace w f),
    lam f

/-- `lam` is a `k`-flower: every 2-dimensional face has weight zero, and there are a vertex `v`
and `l ≤ k/2` such that the edges through `v` or through its antipode have weight zero, the six
other edges have weight `l`, and the cube itself has weight `k - 2l`. -/
def IsFlower (lam : Face → ℕ) (k : ℕ) : Prop :=
  (∀ f, dim f = 2 → lam f = 0) ∧
    ∃ (v : Vertex) (l : ℕ), 2 * l ≤ k ∧ lam (fun _ => none) = k - 2 * l ∧
      ∀ f, dim f = 1 → lam f = if InFace v f ∨ InFace (fun i => !v i) f then 0 else l

end CornerLemma

open CornerLemma

/-- The corner lemma for the cube (Bourneuf, Carmesin, Kurkofka and Planken,
arXiv:2611.01772, Lemma 4.1). Let `lam` weight the faces of the cube so that each of the three
coordinate cuts has value `k`; the weights of the vertices play no role. If `R` is a vertex
cover of the cube and every cut with a vertex of `R` on each side has value at least `k`, then
`lam` is a `k`-flower. -/
theorem P118 (lam : Face → ℕ) (k : ℕ)
    (hcoord : ∀ i : Fin 3, cutValue lam (Finset.univ.filter fun v => v i = false) = k)
    (R : Finset Vertex) (hR : ∀ u w, Adj u w → u ∈ R ∨ w ∈ R)
    (hcut : ∀ A : Finset Vertex, (∃ r ∈ R, r ∈ A) → (∃ r ∈ R, r ∉ A) → k ≤ cutValue lam A) :
    IsFlower lam k := by
  sorry
