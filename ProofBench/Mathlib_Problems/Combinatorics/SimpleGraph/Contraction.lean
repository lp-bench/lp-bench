import Mathlib.Combinatorics.SimpleGraph.Basic
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

universe u

variable {V : Type u} [Fintype V]

/-- `3`-connectivity, the hypothesis of Tutte's wheel theorem: `G` has more than `3` vertices and
stays connected after removing any set of fewer than `3` vertices. -/
abbrev IsThreeConnected (G : SimpleGraph V) : Prop :=
  G.IsVertexConnected 3

/-- The equivalence relation that identifies the two endpoints of an edge. -/
def contractionRelation (e : Sym2 V) (a b : V) : Prop :=
  a = b ∨ (a ∈ e ∧ b ∈ e)

/-- The setoid used for edge contraction. -/
def contractionSetoid (e : Sym2 V) : Setoid V where
  r := contractionRelation e
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro a b h
      rcases h with rfl | ⟨ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hb, ha⟩
    trans := by
      intro a b c h1 h2
      rcases h1 with rfl | ⟨ha, hb⟩
      · exact h2
      · rcases h2 with rfl | ⟨_, hc⟩
        · exact Or.inr ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hc⟩
  }

/-- Vertex type after contracting edge `e`. -/
def ContractedV (e : Sym2 V) : Type u :=
  Quotient (contractionSetoid e)

noncomputable instance contractedVDecidableEq (e : Sym2 V) :
    DecidableEq (ContractedV e) :=
  Classical.decEq _

noncomputable instance contractedVFintype (e : Sym2 V) :
    Fintype (ContractedV e) :=
  Fintype.ofSurjective (Quotient.mk (contractionSetoid e))
    Quotient.mk_surjective

/-- Contract edge `e` in `G`.  Parallel edges created by contraction are
automatically collapsed because the result is a `SimpleGraph`; loops are
discarded by the `x ≠ y` condition. -/
def SimpleGraph.contractEdge (G : SimpleGraph V) (e : Sym2 V) :
    SimpleGraph (ContractedV e) where
  Adj x y :=
    x ≠ y ∧
      ∃ u v : V,
        Quotient.mk (contractionSetoid e) u = x ∧
        Quotient.mk (contractionSetoid e) v = y ∧
        G.Adj u v
  symm := ⟨by
    rintro x y ⟨hne, u, v, rfl, rfl, huv⟩
    exact ⟨hne.symm, v, u, rfl, rfl, huv.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
