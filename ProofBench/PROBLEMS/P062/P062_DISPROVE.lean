/-
Prove-or-disprove companion — DISPROVE polarity for P062 (Tutte's 5-flow
conjecture).

`P062` (in `P062.lean`) and `P062_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The conjecture is OPEN since 1954.  A disproof must exhibit a bridgeless
multigraph with no nowhere-zero `ZMod 5`-flow.  Constraints on any
counterexample: it has a nowhere-zero 6-flow (Seymour) and even an 8-flow
(Jaeger); the conjecture holds for planar graphs (it is the dual of the
Five Colour Theorem) and for graphs with a Hamilton cycle; and by Kochol's
reductions a minimal counterexample is a cyclically 6-edge-connected snark
of girth at least 11.  The Petersen graph — which shows `5` would be best
possible, having no nowhere-zero 4-flow — does have a 5-flow.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.Flow

open Multigraph

universe u v

/-- Disproof polarity of Tutte's 5-flow conjecture: some bridgeless
multigraph has no nowhere-zero `ZMod 5`-flow. -/
theorem P062_disprove :
    ¬ ∀ (V : Type u) (E : Type v) [Fintype E] [DecidableEq V]
        (M : Multigraph V E),
        M.Bridgeless → ∃ f : E → ZMod 5, M.IsNowhereZeroFlow f := by
  sorry
