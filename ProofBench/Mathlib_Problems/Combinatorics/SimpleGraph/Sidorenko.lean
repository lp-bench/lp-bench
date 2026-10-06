import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-!
# Shared definitions for Sidorenko's conjecture (half-graphs)

Used by both `challenge_04` (specific `r`) and `challenge_04_univ` (∀r), so
the half-graph, homomorphism density, and the Sidorenko inequality live here.
-/

open SimpleGraph

/-- The half-graph `H_r` on `Fin r ⊕ Fin r`: `Sum.inl i` and `Sum.inr j` are
adjacent iff `i ≤ j`, with no other edges. Built with `fromRel`, which
symmetrizes the relation and removes self-loops. -/
noncomputable def halfGraph (r : ℕ) : SimpleGraph (Sum (Fin r) (Fin r)) :=
  SimpleGraph.fromRel fun a b =>
    ∃ i j : Fin r, a = Sum.inl i ∧ b = Sum.inr j ∧ i ≤ j

/-- The homomorphism density `t(H, G)`: the number of graph homomorphisms
`H → G` (adjacency-preserving maps), divided by `|V(G)| ^ |V(H)|`. -/
noncomputable def homDensity {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) : ℝ :=
  (Nat.card {f : W → V // ∀ ⦃a b : W⦄, H.Adj a b → G.Adj (f a) (f b)} : ℝ) /
    (Fintype.card V : ℝ) ^ Fintype.card W

/-- Sidorenko's inequality for a (bipartite) graph `H` over `G`, in normalized
homomorphism-density form: `t(H, G) ≥ t(K₂, G) ^ e(H)`, where `t(K₂, G)` is the
edge density (the homomorphism density of the single edge `K₂`) and `e(H)` is
the number of edges of `H`. -/
def SidorenkoFor {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  homDensity H G ≥ homDensity (completeGraph (Fin 2)) G ^ Nat.card H.edgeSet

/-- Homomorphisms from `K₂` correspond to a vertex together with a
neighbour: they count the ordered edges. -/
def edgeHomEquiv {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    {f : Fin 2 → V // ∀ ⦃a b : Fin 2⦄,
        (completeGraph (Fin 2)).Adj a b → G.Adj (f a) (f b)} ≃
      Σ v : V, G.neighborSet v where
  toFun f := ⟨f.1 0, ⟨f.1 1, f.2 (by simp [completeGraph_eq_top])⟩⟩
  invFun p := ⟨fun i => if i = 0 then p.1 else (p.2 : V), by
    intro a b hab
    rw [completeGraph_eq_top, top_adj] at hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · have h : G.Adj p.1 (p.2 : V) := p.2.2
      simpa using h
    · have h : G.Adj p.1 (p.2 : V) := p.2.2
      simpa using h.symm
    · exact absurd rfl hab⟩
  left_inv := by
    rintro ⟨f, hf⟩
    ext i
    fin_cases i <;> simp
  right_inv := by
    rintro ⟨v, w⟩
    simp
