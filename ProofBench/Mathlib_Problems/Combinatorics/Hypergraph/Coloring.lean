import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.Basic

open Finset

namespace FinHypergraph

variable {α : Type*}

/-- A `k`-coloring `color : α → Fin k` is polychromatic for `H`: every hyperedge
contains a vertex of each color. -/
def Polychromatic (H : FinHypergraph α) (k : ℕ) (color : α → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∀ i : Fin k, ∃ v ∈ e, color v = i

/-- `H` admits a polychromatic `k`-coloring. -/
def IsPolychromaticColorable (H : FinHypergraph α) (k : ℕ) : Prop :=
  ∃ color : α → Fin k, H.Polychromatic k color

/-- `X` is a `t`-shallow hitting set of `H`: it meets every hyperedge at least
once and at most `t` times, `1 ≤ |e ∩ X| ≤ t`. -/
def ShallowHittingSet [DecidableEq α] (H : FinHypergraph α) (X : Finset α) (t : ℕ) : Prop :=
  ∀ e ∈ H.edges, 1 ≤ (e ∩ X).card ∧ (e ∩ X).card ≤ t

/-- The finite set `e` is captured by `range` in `H`: it is exactly the set of
vertices of `H` lying in `range`, `e = V(H) ∩ range`. Only the vertex set of `H`
matters. -/
def CapturedBy (H : FinHypergraph α) (e : Finset α) (range : Set α) : Prop :=
  (↑e : Set α) = ↑H.vertices ∩ range

/-- Pointwise form of capture: `p ∈ e ↔ p ∈ V(H) ∧ p ∈ range`. -/
theorem capturedBy_iff {H : FinHypergraph α} {e : Finset α} {range : Set α} :
    H.CapturedBy e range ↔ ∀ p, p ∈ e ↔ p ∈ H.vertices ∧ p ∈ range := by
  simp [CapturedBy, Set.ext_iff]

/-- A captured set consists of vertices of `H`. -/
theorem capturedBy_subset {H : FinHypergraph α} {edge : Finset α} {range : Set α}
    (h : H.CapturedBy edge range) : edge ⊆ H.vertices := by
  intro p hp
  exact (((capturedBy_iff.mp h) p).mp hp).1

/-- An edge is monochromatic under `c`: all its vertices share a color. -/
def Monochromatic {k : ℕ} (c : α → Fin k) (e : Finset α) : Prop :=
  ∀ u ∈ e, ∀ v ∈ e, c u = c v

/-- A weak (proper) `k`-coloring: no hyperedge with at least two vertices is
monochromatic (edges with at most one vertex are exempt, as usual). -/
def WeakColoring (H : FinHypergraph α) (k : ℕ) (c : α → Fin k) : Prop :=
  ∀ e ∈ H.edges, 2 ≤ e.card → ¬ Monochromatic c e

/-- A strong `k`-coloring: distinct vertices of a common hyperedge get distinct
colors. -/
def StrongColoring (H : FinHypergraph α) (k : ℕ) (c : α → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∀ u ∈ e, ∀ v ∈ e, u ≠ v → c u ≠ c v

/-- `H` admits a proper (weak) `k`-coloring. -/
def IsProperlyColorable (H : FinHypergraph α) (k : ℕ) : Prop :=
  ∃ c : α → Fin k, H.WeakColoring k c

/-- `H` admits a strong `k`-coloring. -/
def IsStronglyColorable (H : FinHypergraph α) (k : ℕ) : Prop :=
  ∃ c : α → Fin k, H.StrongColoring k c

end FinHypergraph
