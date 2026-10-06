import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Finite

/-- Dirac: a finite simple graph on at least three vertices, with every
degree at least half its order, has a Hamiltonian cycle. -/
theorem P093 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ v, Fintype.card V ≤ 2 * G.degree v) : G.IsHamiltonian := by
  sorry
