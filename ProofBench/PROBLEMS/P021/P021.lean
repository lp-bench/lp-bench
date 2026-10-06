import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Sidorenko

/-!
# Sidorenko's Conjecture for Half-Graphs

For each `r`, the half-graph `H_r` is the bipartite graph on vertex set
`Fin r ⊕ Fin r` with `(Sum.inl i, Sum.inr j)` adjacent iff `i ≤ j`.

Sidorenko's conjecture for `H_r` states that for every graph `G`, the
homomorphism density `t(H_r, G)` is at least `t(K₂, G)^{|E(H_r)|}`.

`halfGraph`, `homDensity`, and `SidorenkoFor` live in
`ProofBench/Mathlib/Combinatorics/SimpleGraph/Sidorenko.lean`.
-/

open SimpleGraph

variable {V : Type*} [Fintype V]

/-- Sidorenko's conjecture for the half-graph `H_r`. -/
theorem P021 : ∀ r : ℕ, ∀ (G : SimpleGraph V), SidorenkoFor (halfGraph r) G := sorry
