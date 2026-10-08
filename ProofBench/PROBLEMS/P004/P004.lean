import Mathlib.Combinatorics.SimpleGraph.Bipartite
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Sidorenko

/-!
# Sidorenko's Conjecture for Bipartite Graphs
-/

open SimpleGraph

variable {W V : Type*} [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)

/- Sidorenko's Conjecture for the graph `H` over the host `G`: if `H` is
bipartite, the homomorphism-density inequality `t(H, G) ≥ t(K₂, G)^{e(H)}`
holds. -/
def SidorenkoConj : Prop :=
  ∀ ⦃X Y : Set W⦄, H.IsBipartiteWith X Y → SidorenkoFor H G

/-- **Refuting Sidorenko's Conjecture.**  Sidorenko's conjecture asserted the
inequality `t(H, G) ≥ t(K₂, G)^{e(H)}` for every bipartite `H` and every
nonempty finite host `G`.  It was disproved in October 2026 (OpenAI math
release, Lean-checked).  Show that some bipartite `H` and some nonempty finite
host `G` violate it. -/
theorem P004 :
    ¬ ∀ (W V : Type) [Fintype W] [Fintype V] [Nonempty V]
        (H : SimpleGraph W) (G : SimpleGraph V), SidorenkoConj H G := sorry
