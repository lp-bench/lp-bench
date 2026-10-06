import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Automorphism

universe u

open SimpleGraph

/-- Negation of `P081`: a finite connected vertex-transitive graph without a Hamiltonian
path. -/
theorem P081_disprove :
    ¬ (∀ {V : Type u} [Fintype V] (G : SimpleGraph V), G.Connected → VertexTransitive G →
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length + 1 = Fintype.card V) := by
  sorry
