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

/-- The universal Sidorenko conjecture for bipartite graphs. -/
theorem P004 [Nonempty V] : SidorenkoConj H G := sorry
