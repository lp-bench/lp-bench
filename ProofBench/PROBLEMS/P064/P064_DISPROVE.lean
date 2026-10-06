/-
Prove-or-disprove companion — DISPROVE polarity for P064 (the
Berge–Fulkerson conjecture).

`P064` (in `P064.lean`) and `P064_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The conjecture is OPEN since 1971.  A disproof must exhibit a bridgeless
cubic multigraph with no six perfect matchings covering every edge exactly
twice.  Constraints on any counterexample: `3`-edge-colourable cubic graphs
satisfy the conjecture (the colour classes taken twice — proved outright in
`P064_UB_1`), so a counterexample is a snark; the Petersen graph satisfies
it (its six perfect matchings cover every edge exactly twice), as do all
snark families for which the conjecture has been verified; by Mazzuoccolo's
theorem the conjecture is equivalent to Berge's five-matching conjecture,
so a disproof also refutes that; and it would refute the Fan–Raspaud
three-matching conjecture for the counterexample graph (`P064_LB_2`).

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.EdgeColoring

open Multigraph

universe u v

/-- Disproof polarity of the Berge–Fulkerson conjecture: some bridgeless
cubic multigraph has no six perfect matchings covering every edge exactly
twice. -/
theorem P064_disprove :
    ¬ ∀ (V : Type u) (E : Type v) [Fintype E] [DecidableEq V] [DecidableEq E]
        (M : Multigraph V E),
        (∀ e, ¬M.IsLoop e) → M.IsRegular 3 → M.Bridgeless →
        ∃ P : Fin 6 → Finset E, (∀ i, M.IsPerfectMatchingSet (P i)) ∧
          ∀ e : E, (Finset.univ.filter fun i => e ∈ P i).card = 2 := by
  sorry
