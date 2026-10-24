import Mathlib.Combinatorics.SimpleGraph.Basic

open Finset

variable {V : Type*}

/-- A complete bipartite subgraph ("biclique") of the complete graph on `V`,
given by its two disjoint sides. -/
structure Biclique (V : Type*) where
  left : Finset V
  right : Finset V
  disjoint : Disjoint left right

/-- The unordered edge `s(x, y)` is covered by this biclique when one endpoint
lies in `left` and the other in `right`. -/
def Biclique.Covers (b : Biclique V) (e : Sym2 V) : Prop :=
  ∃ x y, x ∈ b.left ∧ y ∈ b.right ∧ e = s(x, y)

/-- `B` is a *biclique partition* of the complete graph on `V`:
every non-loop edge is covered by exactly one of the bicliques `B k`. -/
def IsBicliquePartition {m : ℕ} (B : Fin m → Biclique V) : Prop :=
  ∀ e : Sym2 V, ¬ e.IsDiag → ∃! k, (B k).Covers e

/-- The Graham–Pollak conclusion for a family of `m` bicliques on `Fin n`:
at least `n − 1` bicliques are used, i.e. `n ≤ m + 1`. -/
def GrahamPollakBound {n m : ℕ} (_B : Fin m → Biclique (Fin n)) : Prop :=
  n ≤ m + 1

/- Do not modify above this line. -/

/-- Graham–Pollak theorem (Graham–Pollak 1971, Bell System Tech. J.): any biclique partition of
`Kₙ` uses at least `n − 1` bicliques. -/
theorem P019 {n m : ℕ} (B : Fin m → Biclique (Fin n))
    (h : IsBicliquePartition B) : GrahamPollakBound B := by
  sorry
