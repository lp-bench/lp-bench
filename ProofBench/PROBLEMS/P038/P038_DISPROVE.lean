/-
Prove-or-disprove companion — DISPROVE polarity for P038 (Thomassen's
Conjecture: 4-connected line graphs are Hamiltonian).

`P038` (in `P038.lean`) and `P038_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

Thomassen's conjecture (1986) is a famous OPEN problem, so the truth value of
this polarity is genuinely unknown: a sorry-free proof of `P038_disprove`
would refute the conjecture (and, by Ryjáček's closure theorem, the
Matthews–Sumner conjecture with it).

**Where to look for a counterexample.**  Tomáš Kaiser (personal
communication) believes a counterexample should exist already among line
graphs of CUBIC (3-regular) graphs, though none is known.  For a connected
cubic graph `G`, the line graph `L(G)` is 4-connected iff `G` is essentially
4-edge-connected, and `L(G)` is Hamiltonian iff `G` has a dominating cycle
(Harary–Nash-Williams), so a counterexample is exactly an essentially
4-edge-connected cubic graph without a dominating cycle — a counterexample to
Fleischner's dominating cycle conjecture.  By Fleischner–Jackson, this cubic
restriction is in fact EQUIVALENT to the full conjecture, so nothing is lost
by hunting there.  The statement `P038_disprove_cubic` below records this
restricted search target; `P038_disprove_of_cubic` verifies (sorry-free) that
a cubic counterexample refutes the general conjecture.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).
-/
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Finite
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

universe u

open SimpleGraph

/-- **Disprove version of P038.**  The negation of Thomassen's conjecture:
some finite simple graph `G` has a 4-connected but non-Hamiltonian line
graph.

Thomassen's conjecture is open, so this statement's truth value is genuinely
unknown: proving it refutes the conjecture. -/
theorem P038_disprove :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian := by
  sorry

/-- **Cubic disprove version of P038** (Kaiser's suggested hunting ground).
Some finite CUBIC graph `G` has a 4-connected but non-Hamiltonian line graph;
equivalently, some essentially 4-edge-connected cubic graph has no dominating
cycle.  This refutes Fleischner's dominating cycle conjecture, and by
Fleischner–Jackson it is equivalent to `P038_disprove`; the easy direction is
`P038_disprove_of_cubic` below. -/
theorem P038_disprove_cubic :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
        (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian := by
  sorry

/-- A counterexample among line graphs of cubic graphs is in particular a
counterexample: `P038_disprove_cubic` implies `P038_disprove`. -/
theorem P038_disprove_of_cubic (h : ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.IsRegularOfDegree 3 →
      (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian) :
    ¬ ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        (lineGraph G).IsVertexConnected 4 → (lineGraph G).IsHamiltonian := by
  intro hall
  exact h fun V _ _ G _ _ h4 => hall V G h4
