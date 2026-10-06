import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

namespace Bipartite

variable {L R : Type*} [DecidableEq R]

/-- `N(S)`: the neighbourhood of a set `S` of left vertices of a bipartite
graph presented by the neighbourhood function `nbr` of its left side. -/
def nbhd (nbr : L → Finset R) (S : Finset L) : Finset R :=
  S.biUnion nbr

/-- The fibre of a right vertex `v` over `S`: the vertices of `S` adjacent to
`v`; its cardinality is the degree of `v` in the subgraph induced by `S`. -/
def fibre (nbr : L → Finset R) (S : Finset L) (v : R) : Finset L :=
  S.filter fun u => v ∈ nbr u

/-- `v` is a *unique neighbour* of `S`: exactly one vertex of `S` is adjacent
to `v`. -/
def IsUniqueNeighbour (nbr : L → Finset R) (S : Finset L) (v : R) : Prop :=
  (fibre nbr S v).card = 1

/-- Every left vertex has exactly `c` neighbours. -/
def LeftRegular (nbr : L → Finset R) (c : ℕ) : Prop :=
  ∀ u : L, (nbr u).card = c

/-- Every right vertex has exactly `d` neighbours. -/
def RightRegular [Fintype L] (nbr : L → Finset R) (d : ℕ) : Prop :=
  ∀ v : R, (fibre nbr Finset.univ v).card = d

/-- A `(c, d)`-biregular *unique-neighbour expander family*: a uniform
threshold `δ > 0` and `(c, d)`-biregular bipartite graphs of arbitrarily
large order in which every nonempty set of at most `δ |L|` left vertices
has a unique neighbour. -/
def UniqueNeighbourExpanderFamily (c d : ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ n₀ : ℕ, ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R)
    (_ : DecidableEq R) (nbr : L → Finset R),
    n₀ ≤ Fintype.card L + Fintype.card R ∧ LeftRegular nbr c ∧
      RightRegular nbr d ∧
      ∀ S : Finset L, S.Nonempty → (S.card : ℝ) ≤ δ * Fintype.card L →
        ∃ v : R, IsUniqueNeighbour nbr S v

end Bipartite
