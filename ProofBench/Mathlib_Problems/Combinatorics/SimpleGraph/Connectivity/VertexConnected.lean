module

public import Mathlib.SetTheory.Cardinal.Finite
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.Connected
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Separation

public import Mathlib.Data.Set.Card
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Maps
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Paths

@[expose] public section
variable {V W : Type*} {G : SimpleGraph V} {u v v₁ v₂ w : V} {k l : ℕ}

namespace SimpleGraph

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after removing any
set of fewer than `k` vertices. -/
def IsVertexConnected (k : ℕ) (G : SimpleGraph V) : Prop :=
  k < ENat.card V ∧ ∀ ⦃s : Set V⦄, s.encard < k → G.ConnectedOn sᶜ

/-- An `l`-connected graph is `k`-connected for every `k ≤ l`. -/
lemma IsVertexConnected.mono (hkl : k ≤ l) : G.IsVertexConnected l → G.IsVertexConnected k :=
  fun ⟨hV, hG⟩ ↦ ⟨hV.trans_le' <| by gcongr, fun s hs ↦ hG <| hs.trans_le <| by gcongr⟩

/-- A `k`-connected graph has a vertex. -/
lemma IsVertexConnected.nonempty (hG : G.IsVertexConnected k) : Nonempty V := by
  simpa [ENat.card_pos_iff_nonempty] using bot_le.trans_lt hG.1

/-- `S` separates `A` from `B` in `G`: no `A`–`B` walk avoids `S`. -/
def Separates (G : SimpleGraph V) (S A B : Set V) : Prop :=
  ¬ ∃ a ∈ A, ∃ b ∈ B, G.ReachableOn (Sᶜ) a b

namespace Walk

end Walk

/-- `{A, B}` is a separation of `G`: `A ∪ B = V(G)` and no edge joins `A \ B` to `B \ A`.
It is the `Set` version, for possibly infinite graphs, of the structure `Separation`. -/
def IsSeparation (G : SimpleGraph V) (A B : Set V) : Prop :=
  A ∪ B = Set.univ ∧ ∀ ⦃x y : V⦄, G.Adj x y → ¬ (x ∈ A \ B ∧ y ∈ B \ A)

variable [Fintype V] [DecidableEq V]

/-- A separation `(A, B)` is proper if `A \ B` and `B \ A` are both nonempty. -/
def Separation.IsProper (sep : Separation G) : Prop :=
  (sep.A \ sep.B).Nonempty ∧ (sep.B \ sep.A).Nonempty

/-- Quasi-`k`-connectivity (Grohe): `(k - 1)`-connected, and every proper separation `(A, B)` of
order at most `k - 1` has `|A \ B| = 1` or `|B \ A| = 1`. -/
def QuasiKConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  IsVertexConnected (k - 1) G ∧
    ∀ S : Separation G, S.IsProper → S.order ≤ k - 1 →
      (S.A \ S.B).card = 1 ∨ (S.B \ S.A).card = 1

end SimpleGraph
