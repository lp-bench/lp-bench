/-
Prove-or-disprove companion — DISPROVE polarity for P063 (Mader's
connectivity conjecture).

`P063` (in `P063.lean`) and `P063_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The conjecture is OPEN since 1979.  A disproof must exhibit a graph of
average degree at least `3 * k - 1` with no `(k + 1)`-connected subgraph.
Constraints on any counterexample: average degree `4 * k - 2` suffices
(Mader 1972), so a counterexample has average degree below that; minimum
degree `3 * k - 1` suffices (Krone 2025), so a counterexample contains a
vertex of degree at most `3 * k - 2`; and if the conjecture is true the
bound `3 * k - 1` is sharp for every value of the core connectivity.  By
Carmesin's construction there are graphs of average degree
`(3 + 1/3) * k - O(1)` with no `(k + 1)`-connected subgraph on more than
`2 * k` vertices, so in the regime between `3 * k - 1` and roughly
`(10/3) * k` any highly connected subgraph must be small — a disproof would
have to rule out the small subgraphs as well.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.AverageDegree
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

open SimpleGraph

universe u

/-- Disproof polarity of Mader's connectivity conjecture: some graph of
average degree at least `3 * k - 1` has no `(k + 1)`-connected subgraph. -/
theorem P063_disprove :
    ¬ ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (k : ℕ), 1 ≤ k → (3 * k - 1 : ℚ) ≤ G.averageDegree →
        ∃ s : Set V, (G.induce s).IsVertexConnected (k + 1) := by
  sorry
