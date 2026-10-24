import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Automorphism

universe u

open SimpleGraph

/-- **Lovász's Hamiltonian-path question** (Lovász 1969; Open Problem Garden): every finite
connected vertex-transitive simple graph has a Hamiltonian path, i.e. a path with as many
vertices (`length + 1`) as the graph. -/
theorem P081 : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), G.Connected → VertexTransitive G →
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length + 1 = Fintype.card V := by
  sorry
