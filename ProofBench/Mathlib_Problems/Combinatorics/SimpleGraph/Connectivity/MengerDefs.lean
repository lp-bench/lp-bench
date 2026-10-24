import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Lattice.Nat
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation

noncomputable section

open SimpleGraph Walk Sum

variable {V : Type*} {G : SimpleGraph V}

variable [DecidableEq V]

namespace SimpleGraph

namespace Path

/-- The set of vertices of the path `p`. -/
def Vertices {G : SimpleGraph V} {u v : V} (p : G.Path u v) : Finset V :=
  p.val.support.toFinset

/-- The internal vertices of a `u`–`v` path: its vertices other than `u` and `v`. -/
def internalVertices {G : SimpleGraph V} {u v : V} (p : G.Path u v) : Finset V :=
  p.Vertices \ {u, v}

end Path

end SimpleGraph

/-- A path from a vertex of `S` to a vertex of `T`; its other vertices may also lie in `S`
or `T`. -/
structure STPath (G : SimpleGraph V) (S T : Set V) where
  startVertex : V
  endVertex : V
  path : G.Path startVertex endVertex
  start_in_S : startVertex ∈ S
  end_in_T : endVertex ∈ T

/-- A family of `n` paths (of type `α`) whose vertex sets `support` are pairwise disjoint. -/
structure DisjointPathFamily (G : SimpleGraph V) (α : Type*) (n : ℕ)
    (support : α → Finset V) where
  paths : Fin n → α
  dis : ∀ i j, i ≠ j → Disjoint (support (paths i)) (support (paths j))

/-- The maximum `n` for which a family of `n` pairwise disjoint paths exists. -/
def maxDisjointFamily (G : SimpleGraph V) (α : Type*)
    (support : α → Finset V) : ℕ :=
  sSup {n | Nonempty (DisjointPathFamily G α n support)}

/-- A family of `n` internally disjoint `s`–`t` paths. -/
abbrev InternallyDisjointPaths (G : SimpleGraph V) (s t : V) (n : ℕ) :=
  DisjointPathFamily G (G.Path s t) n (fun p => p.internalVertices)

/-- A family of `n` pairwise vertex-disjoint `S`–`T` paths. -/
abbrev DisjointSTPaths (G : SimpleGraph V) (S T : Set V) (n : ℕ) :=
  DisjointPathFamily G (STPath G S T) n (fun p => p.path.Vertices)

/-- The maximum number of internally disjoint `s`–`t` paths. -/
def maxInternallyDisjointPaths (G : SimpleGraph V) (s t : V) : ℕ :=
  maxDisjointFamily G (G.Path s t) (fun p => p.internalVertices)

/-- The maximum number of pairwise vertex-disjoint `S`–`T` paths. -/
def maxDisjointPaths (G : SimpleGraph V) (S T : Set V) : ℕ :=
  maxDisjointFamily G (STPath G S T) (fun p => p.path.Vertices)

variable [Fintype V]

/-- `κ_G(S, T)`: the minimum order of a separation `(A, B)` of `G` with `S ⊆ A` and `T ⊆ B`. -/
def κ_ST (G : SimpleGraph V) (S T : Set V) : ℕ :=
  sInf {k | ∃ sep : Separation G, S ⊆ sep.A ∧ T ⊆ sep.B ∧ sep.order = k}

/-- **Menger's theorem, set version**: for `S, T ⊆ V(G)`, the maximum number
of pairwise vertex-disjoint `S`–`T` paths equals the minimum order of an
`S`–`T` separation. -/
def menger_v1_prop : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) (S T : Set V),
    maxDisjointPaths G S T = κ_ST G S T

/-- `κ_G(s, t)`: the minimum order of a separation `(A, B)` of `G` with `s ∈ A \ B` and
`t ∈ B \ A`. -/
def κ_st (G : SimpleGraph V) (s t : V) : ℕ :=
  sInf {k | ∃ sep : G.Separation, s ∈ (sep.A \ sep.B) ∧ t ∈ (sep.B \ sep.A) ∧ sep.order = k}

/-- **Menger's theorem, vertex version**: for distinct non-adjacent `s, t`,
the maximum number of pairwise internally disjoint `s`–`t` paths equals the
minimum order of an `s`–`t` separation. -/
def menger_v2_prop : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
   (G : SimpleGraph V) (s t : V), (hst : s ≠ t) -> (hadj : ¬G.Adj s t) ->
    maxInternallyDisjointPaths G s t = κ_st G s t
