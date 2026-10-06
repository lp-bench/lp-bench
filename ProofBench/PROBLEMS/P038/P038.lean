import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected

/-
## Introduction
Thomassen's Conjecture (1986): every 4-connected line graph is Hamiltonian.

The line graph `L(G)` of a simple graph `G` has the edges of `G` as its
vertices, two of them adjacent iff the corresponding edges of `G` share an
endvertex (Mathlib's `SimpleGraph.lineGraph`).  Since every line graph is by
definition of the form `lineGraph G` for some simple graph `G`, the conjecture
is stated here by quantifying over the base graph `G`.

Known partial results include:
* every 7-connected line graph is Hamiltonian (Zhan 1991);
* every 5-connected line graph of minimum degree at least 6 is Hamiltonian
  (Kaiser–Vrána 2012), via a theorem on disjoint spanning trees;
* by Ryjáček's closure, the conjecture is equivalent to the Matthews–Sumner
  conjecture that every 4-connected claw-free graph is Hamiltonian (see
  `P038_UB.lean`).

By a classical theorem of Harary and Nash-Williams, `L(G)` (with at least
three edges in `G`) is Hamiltonian iff `G` has a dominating closed trail, and
`L(G)` is 4-connected iff `G` is essentially 4-edge-connected; so the
conjecture is equivalent to the statement, purely about `G`, that every
essentially 4-edge-connected graph has a dominating closed trail.  Restricted
to cubic `G` this is Fleischner's dominating cycle conjecture, and by
Fleischner–Jackson this restriction is already equivalent to the full
conjecture (see `P038_DISPROVE.lean` for the counterexample-hunting variant).
-/

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Thomassen's Conjecture (1986).**  Every 4-connected line graph is
Hamiltonian: if the line graph of a finite simple graph `G` is 4-connected,
then it has a Hamiltonian cycle. -/
theorem P038 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h4 : (lineGraph G).IsVertexConnected 4) :
    (lineGraph G).IsHamiltonian := by
  sorry
