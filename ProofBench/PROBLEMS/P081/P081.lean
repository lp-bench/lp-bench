import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Automorphism

universe u

open SimpleGraph

/-- **Lovász's Hamiltonian-path question** (1969; Open Problem Garden, "Hamiltonian paths and
cycles in vertex transitive graphs").  Every finite connected vertex-transitive simple graph
has a Hamiltonian path: a path with `n` vertices, `n` the number of vertices of the graph
(equivalently a walk visiting every vertex exactly once, `Walk.IsHamiltonian`; see
`Walk.isHamiltonian_iff_isPath_and_length_eq`).  Vertex-transitivity is the
transitivity of the automorphism group `G ≃g G` on the vertices (`VertexTransitive`, the
vocabulary behind P025); the path, not a cycle, is asked for (`K₂`, the Petersen graph, the
Coxeter graph and their truncations have no Hamiltonian cycle). -/
theorem P081 : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), G.Connected → VertexTransitive G →
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length + 1 = Fintype.card V := by
  sorry
