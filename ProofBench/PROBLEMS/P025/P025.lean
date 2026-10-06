/-
## Introduction
This file challenges you to prove **Theorem 1 of Kurkofka–Planken**,
*A characterisation of all vertex-transitive finite graphs of connectivity < 5*:

> A quasi-4-connected finite graph `G` is vertex-transitive **if and only if**
> `G` is one of ten explicitly described graph families.

The ten alternatives are bundled as `TheoremOneAlternatives G` below; they
range over regular quasi-5-connected graphs, `K₄`/`C₄`-expansions, the prism,
the line graph of the cube, and several *cycle-decomposition* families
(cycles of `K₄`-, `C₄`-, `K₂,₂`-, or triangle-bags) in the sense of
Definition 2.3 of the paper.

The supporting vocabulary is fixed setup:

* `QuasiKConnected`, `Separation`  — from `…Connectivity.VertexConnected`;
* the cycle-decomposition classes
  `GraphDecomp G (cycleGraph l)`);
* `HExpansion` / `IsExpansion`  — the `H`-expansion construction (replace each
  vertex by a copy of `H`, each edge by a perfect matching).

Only the final `theorem P025` is to be proved.
-/

import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Automorphism
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Connectivity.VertexConnected
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.CyclicDecomposition
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Expansion

open SimpleGraph
open Cyclic_Decomposition

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The paper's `2`-quasi-5-connected condition. -/
def TwoQuasi5Connected (G : SimpleGraph V) : Prop :=
  QuasiKConnected G 4 ∧
    ∀ S : Separation G, S.order ≤ 4 →
      (S.A \ S.B).card ≤ 2 ∨ (S.B \ S.A).card ≤ 2

/-- `Gexp` is a `K₃`-expansion of `G`. -/
def IsK3Expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (Gexp : SimpleGraph (V × Fin 3)) : Prop :=
  IsExpansion (completeGraph (Fin 3)) G Gexp

/-- `Gexp` is a `K₄`-expansion of `G`. -/
def IsK4Expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (Gexp : SimpleGraph (V × Fin 4)) : Prop :=
  IsExpansion (completeGraph (Fin 4)) G Gexp

/-- `Gexp` is a `C₄`-expansion of `G`. -/
def IsC4Expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (Gexp : SimpleGraph (V × Fin 4)) : Prop :=
  IsExpansion (cycleGraph 4) G Gexp

/-- `G` is (isomorphic to) the prism `K₃ □ K₂`. -/
def IsPrismGraph (G : SimpleGraph V) : Prop :=
  ∃ e : V ≃ Fin 3 × Fin 2,
    ∀ x y : V, G.Adj x y ↔ (completeGraph (Fin 3) □ completeGraph (Fin 2)).Adj (e x) (e y)

/-- `G` is (isomorphic to) the line graph of the cube `C₄ □ K₂`. -/
def IsLineGraphOfCube (G : SimpleGraph V) : Prop :=
  ∃ e : V ≃ (cycleGraph 4 □ completeGraph (Fin 2)).edgeSet,
    ∀ x y : V, G.Adj x y ↔
      (lineGraph (cycleGraph 4 □ completeGraph (Fin 2))).Adj (e x) (e y)

/-- The three vertex-transitive `C₄`-expansions of the line graph of the cube. -/
def IsOneOfThreeVertexTransitiveC4ExpansionsOfLineGraphOfCube
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  VertexTransitive G ∧
    ∃ (V' : Type u) (_ : Fintype V') (_ : DecidableEq V')
      (G' : SimpleGraph V') (_ : DecidableRel G'.Adj),
      IsLineGraphOfCube G' ∧
        ∃ e : V ≃ V' × Fin 4, IsC4Expansion G' (G.map e)

/-- Case (iii) of Theorem 1. -/
def CaseIII (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (V' : Type u) (_ : Fintype V') (_ : DecidableEq V')
    (G' : SimpleGraph V') (_ : DecidableRel G'.Adj),
    QuasiKConnected G' 5 ∧ G'.IsRegularOfDegree 4 ∧ ArcTransitive G' ∧
      ∃ e : V ≃ V' × Fin 4,
        IsK4Expansion G' (G.map e) ∨
          (VertexTransitive G ∧ IsC4Expansion G' (G.map e))

/-- Case (ix): the base cycle of `K₂,₂`-bags and its expansions. -/
def CaseIX (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∃ l : Nat, IsCycleOfK22Bags G l) ∨
    ∃ (V' : Type u) (_ : Fintype V') (_ : DecidableEq V')
      (G' : SimpleGraph V') (_ : DecidableRel G'.Adj),
      (∃ l : Nat, IsCycleOfK22Bags G' l) ∧
        ∃ e : V ≃ V' × Fin 4,
          IsK4Expansion G' (G.map e) ∨
            (VertexTransitive G ∧ IsC4Expansion G' (G.map e))

/-- Case (x): the line graph of the cube and the expansion variants. -/
def CaseX (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  IsLineGraphOfCube G ∨
    (∃ (V' : Type u) (_ : Fintype V') (_ : DecidableEq V')
      (G' : SimpleGraph V') (_ : DecidableRel G'.Adj),
      IsLineGraphOfCube G' ∧ ∃ e : V ≃ V' × Fin 4, IsK4Expansion G' (G.map e)) ∨
    IsOneOfThreeVertexTransitiveC4ExpansionsOfLineGraphOfCube G

/-- The ten alternatives of Theorem 1. -/
def TheoremOneAlternatives (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (QuasiKConnected G 5 ∧ VertexTransitive G ∧ ∃ d : Nat, 4 ≤ d ∧ G.IsRegularOfDegree d) ∨
  (G.IsRegularOfDegree 3 ∧ TwoQuasi5Connected G ∧ VertexTransitive G) ∨
  CaseIII G ∨
  (∃ l : Nat, IsCycleOfK4Bags G l) ∨
  (∃ l : Nat, IsCycleAlternatingK4C4 G l) ∨
  (∃ l : Nat, IsCycleOfTriangleBags G l) ∨
  (∃ l : Nat, IsCycleAlternatingK22C4 G l) ∨
  ((∃ l : Nat, IsCycleOfC4Bags G l) ∨ IsPrismGraph G) ∨
  CaseIX G ∨
  CaseX G

/- Do not modify above this line. -/

/-- **Theorem 1 (Kurkofka–Planken).** A quasi-4-connected finite graph `G` is
vertex-transitive if and only if `G` is one of the ten families collected in
`TheoremOneAlternatives`. -/
theorem P025 (G : SimpleGraph V) [DecidableRel G.Adj] :
    QuasiKConnected G 4 → (VertexTransitive G ↔ TheoremOneAlternatives G) := by
  sorry
