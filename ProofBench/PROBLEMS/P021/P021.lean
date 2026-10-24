import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Sidorenko

open SimpleGraph

variable {V : Type*} [Fintype V]

/-- Sidorenko's inequality `t(H_r, G) ≥ t(K₂, G) ^ e(H_r)` holds for every half-graph `H_r` and
every finite graph `G`; a case of Conlon–Fox–Sudakov (GAFA 2010). -/
theorem P021 : ∀ r : ℕ, ∀ (G : SimpleGraph V), SidorenkoFor (halfGraph r) G := sorry
