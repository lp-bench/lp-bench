/-
Copyright (c) 2025 ProofBench participants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofBench participants
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.Connected
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation

public import Mathlib.Data.Set.Card
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Maps
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Paths

/-!
# Vertex connectivity
-/

@[expose] public section
variable {V W : Type*} {G : SimpleGraph V} {u v v₁ v₂ w : V} {k l : ℕ}

namespace SimpleGraph

/-- A simple graph is `k`-connected if it is still connected after removing any `k - 1` vertices.

By Menger's theorem, this is equivalent to the property that every `k` pairs of vertices can be
connected by `k` vertex-disjoint paths. -/
def IsVertexConnected (k : ℕ) (G : SimpleGraph V) : Prop :=
  k < ENat.card V ∧ ∀ ⦃s : Set V⦄, s.encard < k → G.ConnectedOn sᶜ

lemma IsVertexConnected.mono (hkl : k ≤ l) : G.IsVertexConnected l → G.IsVertexConnected k :=
  fun ⟨hV, hG⟩ ↦ ⟨hV.trans_le' <| by gcongr, fun s hs ↦ hG <| hs.trans_le <| by gcongr⟩

lemma IsVertexConnected.nonempty (hG : G.IsVertexConnected k) : Nonempty V := by
  simpa [ENat.card_pos_iff_nonempty] using bot_le.trans_lt hG.1

/-!

`Separates G S A B` is the *cut* predicate: no `A`–`B` walk avoids `S`. A *separation* `{A,B}`
is then a cover of `V(G)` whose separator `A ∩ B` separates the two sides — see
`isSeparation_iff_separates`. The bundled finite `Separation` structure further below is the
special case over `Finset V`; `Separation.isSeparation` connects the two. -/

/-- `S` separates `A` from `B` in `G`: no `A`–`B` walk avoids `S`. -/
def Separates (G : SimpleGraph V) (S A B : Set V) : Prop :=
  ¬ ∃ a ∈ A, ∃ b ∈ B, G.ReachableOn (Sᶜ) a b

namespace Walk

end Walk

/-- `{A, B}` is a separation of `G`: it covers `V(G)`, and no edge runs between `A \ B` and
`B \ A`. Equivalently (`isSeparation_iff_separates`), its separator `A ∩ B` separates `A` from `B`.
This is the `Set`-level (possibly infinite) form of the bundled `Separation` structure below. -/
def IsSeparation (G : SimpleGraph V) (A B : Set V) : Prop :=
  A ∪ B = Set.univ ∧ ∀ ⦃x y : V⦄, G.Adj x y → ¬ (x ∈ A \ B ∧ y ∈ B \ A)

variable [Fintype V] [DecidableEq V]

/- A separation is proper if both sides are non-empty outside the separator -/
def Separation.IsProper (sep : Separation G) : Prop :=
  (sep.A \ sep.B).Nonempty ∧ (sep.B \ sep.A).Nonempty

-- /- A k-separation is a separation of order at most k -/
-- def IsKSeparation (G : SimpleGraph V) (k : ℕ) (sep : G.Separation) : Prop :=
--   sep.order ≤ k

/-- Quasi-k-connectivity: k-connected and every k-separation has a one-vertex side. -/
def QuasiKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  IsVertexConnected k G ∧
    ∀ S : Separation G, S.order ≤ k →
      (S.A \ S.B).card = 1 ∨ (S.B \ S.A).card = 1

end SimpleGraph
