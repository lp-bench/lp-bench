/-
## Introduction
Seymour's Second Neighbourhood Conjecture (Paul Seymour, c. 1990).

An *oriented graph* is a directed graph with no loops and no 2-cycles — an
orientation of a simple graph.  For a vertex `v`, its *first out-neighbourhood*
`N⁺(v)` is the set of vertices `v` points to, and its *second out-neighbourhood*
`N⁺⁺(v)` is the set of vertices at directed distance exactly two from `v`
(reachable by a 2-step directed path, but not themselves out-neighbours of `v`).

The conjecture asserts that every finite oriented graph has a vertex `v` with
`|N⁺(v)| ≤ |N⁺⁺(v)|` — a vertex whose second neighbourhood is at least as large
as its first.  The tournament case is Dean's conjecture, proved by Fisher
(1996); the general case was open until October 2026, when a proof appeared in
OpenAI's math release (Lean-checked).

This file challenges you to prove the conjecture.
-/

import Mathlib.Data.Set.Card

/-- An *oriented graph* on a vertex type `V`: an adjacency relation that is
loopless and has no 2-cycles (so it is an orientation of a simple graph). -/
structure OrientedGraph (V : Type*) where
  /-- The directed adjacency relation: `Adj u v` means there is an arc `u → v`. -/
  Adj : V → V → Prop
  /-- No loops. -/
  loopless : ∀ v, ¬ Adj v v
  /-- No 2-cycles: an arc `u → v` forbids the reverse arc `v → u`. -/
  oriented : ∀ u v, Adj u v → ¬ Adj v u

namespace OrientedGraph

variable {V : Type*}

/-- First out-neighbourhood `N⁺(v) = { w | v → w }`. -/
def outNeighborhood (G : OrientedGraph V) (v : V) : Set V :=
  {w | G.Adj v w}

/-- Second out-neighbourhood `N⁺⁺(v)`: vertices at directed distance exactly two
from `v` — reachable by a 2-step directed path, but not out-neighbours of `v`. -/
def secondOutNeighborhood (G : OrientedGraph V) (v : V) : Set V :=
  {w | w ≠ v ∧ ¬ G.Adj v w ∧ ∃ u, G.Adj v u ∧ G.Adj u w}

end OrientedGraph

open OrientedGraph

/- Do not modify above this line. -/

/-- **Seymour's Second Neighbourhood Conjecture (1990).**  Every finite oriented
graph has a vertex whose second out-neighbourhood is at least as large as its
first: `|N⁺(v)| ≤ |N⁺⁺(v)|` (cardinalities via `Set.ncard`). -/
theorem P027 {V : Type*} [Finite V] (G : OrientedGraph V) :
    ∃ v, (G.outNeighborhood v).ncard ≤ (G.secondOutNeighborhood v).ncard := by
  sorry
