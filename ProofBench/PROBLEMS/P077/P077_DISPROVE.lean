/-
Prove-or-disprove companion — DISPROVE polarity for P077 (the 57-regular Moore
graph problem).

`P077` (in `P077.lean`) and `P077_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The problem is OPEN.  A proof of `P077` is an explicit graph on `3250`
vertices — equivalently (`P077_UB_1`) a symmetric `0/1` matrix `A` of order
`3250` with zero diagonal and `A² + A = 56 I + J`, which a kernel-checked
computation could certify.  A disproof must show that no `57`-regular graph
of diameter `2` and girth `5` exists (`P077_UB_2` makes the two formulations
interchangeable).  The parameters pass the Hoffman–Singleton eigenvalue
condition (eigenvalues `7` and `-8` with multiplicities `1729` and `1520`);
it is known that such a graph cannot be vertex-transitive and that its
automorphism group has order at most `375` (Mačaj–Širáň), so a disproof
needs a genuinely new structural argument or a search far beyond current
reach.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- Disproof polarity of the 57-regular Moore graph problem: no strongly regular graph
with parameters `(3250, 57, 0, 1)` exists. -/
theorem P077_disprove :
    ¬ ∃ (G : SimpleGraph (Fin 3250)) (_ : DecidableRel G.Adj), G.IsSRGWith 3250 57 0 1 := by
  sorry
