/-
Copyright (c) 2026 ProofBench participants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofBench participants
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation

noncomputable section

open SimpleGraph Walk Sum

variable {V : Type*} {G : SimpleGraph V}

variable [DecidableEq V]

namespace SimpleGraph

namespace Path

/- Given a path p, then the set of vertices of p.  -/
def Vertices {G : SimpleGraph V} {u v : V} (p : G.Path u v) : Finset V :=
  p.val.support.toFinset

def internalVertices {G : SimpleGraph V} {u v : V} (p : G.Path u v) : Finset V :=
  p.Vertices \ {u, v}

end Path

end SimpleGraph

/- A path from set S to set T -/
structure STPath (G : SimpleGraph V) (S T : Set V) where
  startVertex : V
  endVertex : V
  path : G.Path startVertex endVertex
  start_in_S : startVertex ∈ S
  end_in_T : endVertex ∈ T

/-- A family of n paths, pairwise disjoint on their supports. -/
structure DisjointPathFamily (G : SimpleGraph V) (α : Type*) (n : ℕ)
    (support : α → Finset V) where
  paths : Fin n → α
  dis : ∀ i j, i ≠ j → Disjoint (support (paths i)) (support (paths j))

/-- Maximum n for which such a family exists. -/
def maxDisjointFamily (G : SimpleGraph V) (α : Type*)
    (support : α → Finset V) : ℕ :=
  sSup {n | Nonempty (DisjointPathFamily G α n support)}

/-- Internally disjoint s–t paths. α = G.Path s t -/
abbrev InternallyDisjointPaths (G : SimpleGraph V) (s t : V) (n : ℕ) :=
  DisjointPathFamily G (G.Path s t) n (fun p => p.internalVertices)

/-- Disjoint S–T paths. α = STPath G S T -/
abbrev DisjointSTPaths (G : SimpleGraph V) (S T : Set V) (n : ℕ) :=
  DisjointPathFamily G (STPath G S T) n (fun p => p.path.Vertices)

def maxInternallyDisjointPaths (G : SimpleGraph V) (s t : V) : ℕ :=
  maxDisjointFamily G (G.Path s t) (fun p => p.internalVertices)

def maxDisjointPaths (G : SimpleGraph V) (S T : Set V) : ℕ :=
  maxDisjointFamily G (STPath G S T) (fun p => p.path.Vertices)



variable [Fintype V]

/-
κ_G(S, T) is the minimum order of a separation (A,B) with S ⊆ A and T ⊆ B
-/
def κ_ST (G : SimpleGraph V) (S T : Set V) : ℕ :=
  sInf {k | ∃ sep : Separation G, S ⊆ sep.A ∧ T ⊆ sep.B ∧ sep.order = k}

/-- **Menger's theorem, set version**: for `S, T ⊆ V(G)`, the maximum number
of pairwise vertex-disjoint `S`–`T` paths equals the minimum order of an
`S`–`T` separation. -/
def menger_v1_prop : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (S T : Set V),
    maxDisjointPaths G S T = κ_ST G S T

/-
Given two vertices s and t, κ_G(s, t) is the minimum order
of a separation (A,B) with s ∈ A \ B and t ∈ B \ A.
-/
def κ_st (G : SimpleGraph V) (s t : V) : ℕ :=
  sInf {k | ∃ sep : G.Separation, s ∈ (sep.A \ sep.B) ∧ t ∈ (sep.B \ sep.A) ∧ sep.order = k}

/-- **Menger's theorem, vertex version**: for distinct non-adjacent `s, t`,
the maximum number of pairwise internally disjoint `s`–`t` paths equals the
minimum order of an `s`–`t` separation. -/
def menger_v2_prop : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
   (G : SimpleGraph V) (s t : V), (hst : s ≠ t) -> (hadj : ¬G.Adj s t) ->
    maxInternallyDisjointPaths G s t = κ_st G s t
