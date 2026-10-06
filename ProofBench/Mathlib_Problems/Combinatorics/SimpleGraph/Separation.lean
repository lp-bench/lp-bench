/-
Copyright (c) 2026 ProofBench participants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofBench participants
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An oriented vertex separation `(A, B)` of a finite simple graph: the
sides cover every vertex and no edge joins `A \ B` to `B \ A`. -/
structure Separation (G : SimpleGraph V) where
  A : Finset V
  B : Finset V
  union_eq : A ∪ B = Finset.univ
  no_edge_across : ∀ {u v : V}, G.Adj u v → u ∈ A \ B → v ∉ B \ A

/-- The vertices shared by the two sides of a separation. -/
def Separation.separator {G : SimpleGraph V} (s : G.Separation) : Finset V :=
  s.A ∩ s.B

/-- The order of a separation is the number of vertices in its separator. -/
def Separation.order {G : SimpleGraph V} (s : G.Separation) : ℕ :=
  s.separator.card

/-- Reverse the orientation of a separation. -/
def Separation.flip {G : SimpleGraph V} (s : G.Separation) : G.Separation where
  A := s.B
  B := s.A
  union_eq := by rw [Finset.union_comm, s.union_eq]
  no_edge_across hadj hu hv := s.no_edge_across hadj.symm hv hu

end SimpleGraph
