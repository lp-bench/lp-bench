import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Finite
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

universe u

open SimpleGraph

/-- The negation of Thomassen's conjecture (P038): some finite simple graph `G` has a
4-connected but non-Hamiltonian line graph. -/
theorem P038_disprove :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian := by
  sorry

/-- The cubic version of `P038_disprove`: some finite cubic graph `G` has a 4-connected but
non-Hamiltonian line graph, i.e. Fleischner's dominating cycle conjecture fails. By
Fleischner–Jackson (1989) it is equivalent to `P038_disprove`. -/
theorem P038_disprove_cubic :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
        (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian := by
  sorry

/-- `P038_disprove_cubic` implies `P038_disprove`. -/
theorem P038_disprove_of_cubic (h : ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
      (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian) :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian := by
  intro hall
  exact h fun V _ _ G _ _ h4 => hall V G h4
