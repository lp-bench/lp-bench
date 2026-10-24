import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.Order.Archimedean.Real.Basic

open Function Set

namespace OddHadwiger

universe u

variable {V : Type u}

/-- A model of an odd `K_t` minor in `G`: `t` vertex-disjoint trees in `G`,
each properly two-colored, such that every two of them are joined by an edge
of `G` whose endpoints have the same color. -/
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

/-- The chromatic bound `χ(G) ≥ (3/2 - δ)t` of Theorem 1.3, with the real
bound rounded up (equivalent, since `χ(G)` is an integer or `∞`). -/
def HasPaperChromaticLowerBound (G : SimpleGraph V) (δ : ℝ) (t : ℕ) : Prop :=
  ⌈((3 / 2 : ℝ) - δ) * t⌉₊ ≤ G.chromaticNumber

/-- Theorem 1.3 of Kühn–Sauermann–Steiner–Wigderson, arXiv:2512.20392: for
every `δ > 0` and every sufficiently large `t` there is a finite graph with
chromatic number at least `(3/2 - δ)t` and no odd `K_t` minor. -/
theorem P047 :
    ∀ δ : ℝ, 0 < δ → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        HasPaperChromaticLowerBound G δ t ∧ OddCliqueMinorFree G t := by
  sorry

end OddHadwiger
