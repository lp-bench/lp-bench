/-
Prove-or-disprove companion — DISPROVE polarity for P078 (the Borodin–Kostochka
conjecture).

`P078` (in `P078.lean`) and `P078_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The problem is OPEN.  A disproof is a finite graph with maximum degree
`Δ ≥ 9`, clique number less than `Δ`, and no `(Δ − 1)`-colouring
(`P078_LB_1` shows this is exactly what a counterexample must look like).
The conjecture is known for `Δ ≥ 10¹⁴` (Reed), for claw-free graphs and
several other classes, and a 2026 correspondence-colouring result covers all
sufficiently large `Δ`; a counterexample would therefore have bounded, but
not small, maximum degree.  A proof must handle every `Δ ≥ 9` down to the
threshold, where the Catlin graphs show the bound is sharp.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

universe u

/-- Disproof polarity of the Borodin–Kostochka conjecture: some finite graph with
maximum degree at least `9` has chromatic number exceeding `max (Δ − 1) ω`. -/
theorem P078_disprove :
    ¬ ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      9 ≤ G.maxDegree → G.chromaticNumber ≤ max (G.maxDegree - 1) G.cliqueNum := by
  sorry
