/- Paper: Disproof of the Odd Hadwiger Conjecture (Kühn–Sauermann–Steiner–Wigderson,
arXiv:2512.20392). -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Order.Archimedean.Real.Basic


open Function Set

namespace OddHadwiger

universe u

variable {V : Type u}

/-- A model of an odd `K_t` minor in `G`.

For each vertex of `K_t`, `branch` selects a vertex-disjoint tree subgraph of
`G`. Each branch tree is properly two-colored. Between every two distinct
branches there is an ambient edge whose endpoints receive the same color.
This is exactly the definition used in the paper. -/
structure OddCliqueMinorModel (G : SimpleGraph V) (t : ℕ) where
  /-- The pairwise disjoint branch trees. -/
  branch : Fin t → G.Subgraph
  /-- Every branch subgraph is a tree on its own vertex subtype. -/
  isTree : ∀ i, (branch i).coe.IsTree
  /-- Distinct branch trees have disjoint vertex sets. -/
  vertex_disjoint : Pairwise fun i j => Disjoint (branch i).verts (branch j).verts
  /-- A black/white coloring of each branch tree. -/
  color : ∀ i, (branch i).verts → Bool
  /-- The branch colorings are proper. -/
  color_proper : ∀ i ⦃x y : (branch i).verts⦄,
    (branch i).coe.Adj x y → color i x ≠ color i y
  /-- Every two branch trees are joined by a same-colored ambient edge. -/
  same_color_adjacent : ∀ ⦃i j : Fin t⦄, i ≠ j →
    ∃ (x : (branch i).verts) (y : (branch j).verts),
      G.Adj x.1 y.1 ∧ color i x = color j y

/-- `G` contains an odd clique minor of order `t`. -/
def HasOddCliqueMinor (G : SimpleGraph V) (t : ℕ) : Prop :=
  Nonempty (OddCliqueMinorModel G t)

/-- A graph avoids an odd clique minor of order `t`. -/
def OddCliqueMinorFree (G : SimpleGraph V) (t : ℕ) : Prop :=
  ¬ HasOddCliqueMinor G t

/-- No graph is odd-`K_0`-minor-free: the empty family is a valid model. -/
theorem hasOddCliqueMinor_zero (G : SimpleGraph V) : HasOddCliqueMinor G 0 := by
  classical
  refine ⟨{
    branch := Fin.elim0
    isTree := fun i => Fin.elim0 i
    vertex_disjoint := fun i => Fin.elim0 i
    color := fun i => Fin.elim0 i
    color_proper := fun i => Fin.elim0 i
    same_color_adjacent := fun {i} => Fin.elim0 i
  }⟩

/-- The chromatic lower bound occurring in Theorem 1.3.

The ceiling converts the real-valued expression `(3/2 - δ)t` into the exact
integer lower bound asserted for the chromatic number. -/
def HasPaperChromaticLowerBound (G : SimpleGraph V) (δ : ℝ) (t : ℕ) : Prop :=
  ⌈((3 / 2 : ℝ) - δ) * t⌉₊ ≤ G.chromaticNumber

/-- **Kühn--Sauermann--Steiner--Wigderson, Theorem 1.3.**

For every fixed positive `δ` and every sufficiently large integer `t`, there
is a finite graph whose chromatic number is at least `(3/2 - δ)t` and which
contains no odd `K_t` minor.

The paper proves this from its stronger Theorem 1.4 using a probabilistic
construction of a pseudorandom triangle-free graph and then passing to its
complement. -/
theorem P047 :
    ∀ δ : ℝ, 0 < δ → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        HasPaperChromaticLowerBound G δ t ∧ OddCliqueMinorFree G t := by
  sorry

end OddHadwiger
