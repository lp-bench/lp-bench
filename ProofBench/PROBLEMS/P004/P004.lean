import Mathlib.Combinatorics.SimpleGraph.Bipartite
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Sidorenko

open SimpleGraph

variable {W V : Type*} [Fintype W] [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)

/-- Sidorenko's Conjecture for the graph `H` over the host `G`: if `H` is
bipartite, the homomorphism-density inequality `t(H, G) ≥ t(K₂, G)^{e(H)}`
holds. -/
def SidorenkoConj : Prop :=
  ∀ ⦃X Y : Set W⦄, H.IsBipartiteWith X Y → SidorenkoFor H G

/-- **Refuting Sidorenko's Conjecture** (Sidorenko 1993; disproved in OpenAI's math
release, October 2026): some finite bipartite graph `H` and some nonempty finite
graph `G` satisfy `t(H, G) < t(K₂, G)^{e(H)}`. -/
theorem P004 :
    ¬ ∀ (W V : Type) [Fintype W] [Fintype V] [Nonempty V]
        (H : SimpleGraph W) (G : SimpleGraph V), SidorenkoConj H G := sorry
