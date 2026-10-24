import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Finite
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

universe u

open SimpleGraph

/-- The negation of Thomassen's conjecture (P038): some finite simple graph `G` has a
4-connected but non-Hamiltonian line graph. By Fleischner–Jackson (1989), such a `G` exists if
and only if a cubic one does. -/
theorem P038_disprove :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian := by
  sorry
