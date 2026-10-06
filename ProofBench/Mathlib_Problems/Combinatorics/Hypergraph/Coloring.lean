import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.Basic

/- ==============================================================================
Abstract hypergraph colorings and hitting sets.

This file collects the notions that make sense for an arbitrary hypergraph
`H = (V, E)` over any vertex type `α` — independent of any geometry:

* colorings — `Polychromatic`, `WeakColoring` (proper), `StrongColoring`;
* `ShallowHittingSet`;
* `CapturedBy` (a finite vertex set is exactly `V(H) ∩ range`);

together with the relationships among the three coloring notions and how they
specialize to graphs (`2`-uniform hypergraphs).

The geometric layer — Euclidean space `ℝ^d`, range families, and the
range-capturing hypergraph `H(V, R, m)` — lives in `RangeCapturing.lean`, which
imports this file.
============================================================================== -/

open Finset

namespace Hypergraph

variable {α : Type*}

/- A `k`-coloring `color : α → Fin k` of the vertices is **polychromatic** for
`H` when every hyperedge contains a vertex of each color. -/
def Polychromatic (H : Hypergraph α) (k : ℕ) (color : α → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∀ i : Fin k, ∃ v ∈ e, color v = i

/- `H` **admits a polychromatic `k`-coloring**. -/
def IsPolychromaticColorable (H : Hypergraph α) (k : ℕ) : Prop :=
  ∃ color : α → Fin k, H.Polychromatic k color

/- `X` is a **`t`-shallow hitting set** of `H` (paper, §1.2): it meets every
hyperedge at least once and at most `t` times, `1 ≤ |e ∩ X| ≤ t`. -/
def ShallowHittingSet [DecidableEq α] (H : Hypergraph α) (X : Finset α) (t : ℕ) : Prop :=
  ∀ e ∈ H.edges, 1 ≤ (e ∩ X).card ∧ (e ∩ X).card ≤ t

/- A finite point set `edge` is **captured by** a range `range` in the hypergraph
`H` when it is exactly the set of vertices of `H` lying in `range`, i.e.
`edge = V(H) ∩ range` (paper, §1: `e = V ∩ R`).  Capture is a notion *about the
hypergraph*: it is phrased against the vertex set `H.vertices = V(H)`. -/
def CapturedBy (H : Hypergraph α) (e : Finset α) (range : Set α) : Prop :=
  (↑e : Set α) = ↑H.vertices ∩ range

/- The pointwise view of capture (`p ∈ e ↔ p ∈ V(H) ∧ p ∈ range`), recovered from
the set equation `e = V ∩ range` when destructuring is more convenient. -/
theorem capturedBy_iff {H : Hypergraph α} {e : Finset α} {range : Set α} :
    H.CapturedBy e range ↔ ∀ p, p ∈ e ↔ p ∈ H.vertices ∧ p ∈ range := by
  simp [CapturedBy, Set.ext_iff]

theorem capturedBy_subset {H : Hypergraph α} {edge : Finset α} {range : Set α}
    (h : H.CapturedBy edge range) : edge ⊆ H.vertices := by
  intro p hp
  exact (((capturedBy_iff.mp h) p).mp hp).1

/- ===================================================================
Weak (proper) and strong colorings, and how they relate to polychromatic
colorings and to ordinary graph coloring.

For a hypergraph the three notions of a `k`-coloring `c : α → Fin k` are:
* **weak / proper** — no hyperedge is monochromatic (`WeakColoring`);
* **polychromatic** — every hyperedge contains *all* `k` colors (`Polychromatic`);
* **strong** — `c` is injective on each hyperedge (`StrongColoring`).

A graph is a `2`-uniform hypergraph (`H.IsUniform 2`); under that hypothesis these
notions specialize to the familiar graph picture (see the final group of lemmas).
=================================================================== -/

/-- An edge is **monochromatic** under `c` when all its vertices share a color. -/
def Monochromatic {k : ℕ} (c : α → Fin k) (e : Finset α) : Prop :=
  ∀ u ∈ e, ∀ v ∈ e, c u = c v

/-- A **weak (proper) `k`-coloring**: no hyperedge of size `≥ 2` is monochromatic.
The `2 ≤ e.card` guard is the usual convention — a single-vertex edge is always
monochromatic, so only edges that *can* be non-monochromatic are constrained. -/
def WeakColoring (H : Hypergraph α) (k : ℕ) (c : α → Fin k) : Prop :=
  ∀ e ∈ H.edges, 2 ≤ e.card → ¬ Monochromatic c e

/-- A **strong `k`-coloring**: distinct vertices of a common hyperedge get distinct
colors, i.e. `c` is injective on every hyperedge. -/
def StrongColoring (H : Hypergraph α) (k : ℕ) (c : α → Fin k) : Prop :=
  ∀ e ∈ H.edges, ∀ u ∈ e, ∀ v ∈ e, u ≠ v → c u ≠ c v

/-- `H` admits a proper (weak) `k`-coloring. -/
def IsProperlyColorable (H : Hypergraph α) (k : ℕ) : Prop :=
  ∃ c : α → Fin k, H.WeakColoring k c

/-- `H` admits a strong `k`-coloring. -/
def IsStronglyColorable (H : Hypergraph α) (k : ℕ) : Prop :=
  ∃ c : α → Fin k, H.StrongColoring k c

/-! ### How the three notions relate -/

/-! ### Specialization to graphs (`2`-uniform hypergraphs)

A graph is a `2`-uniform hypergraph: every edge `{u, v}` has exactly two vertices.
-/

end Hypergraph
