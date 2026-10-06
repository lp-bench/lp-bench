/-
Prove-or-disprove companion — DISPROVE polarity for P076 (Conway's 99-graph
problem).

`P076` (in `P076.lean`) and `P076_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The problem is OPEN.  A proof of `P076` is an explicit graph — equivalently
(`P076_UB_1`) a symmetric `0/1` matrix `A` of order `99` with zero diagonal
and `A² = 14 I + A + 2 (J − I − A)`, which a kernel-checked computation could
certify.  A disproof must show that no such graph exists: the parameters
satisfy all known feasibility conditions (integrality of the eigenvalues
`3` and `-4` with multiplicities `54` and `44`, the Krein conditions, the
absolute bound), the local graph at every vertex is `7 K₂`, and strong
restrictions on the automorphism group are known (Makhnev–Minakova), so a
disproof needs a genuinely new structural argument or an exhaustive search
far beyond current reach.  The sibling parameter sets `(9, 4, 1, 2)` (the
Paley graph on nine vertices) and `(243, 22, 1, 2)` (the Berlekamp–van
Lint–Seidel graph) do exist.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-- Disproof polarity of Conway's 99-graph problem: no strongly regular graph with
parameters `(99, 14, 1, 2)` exists. -/
theorem P076_disprove :
    ¬ ∃ (G : SimpleGraph (Fin 99)) (_ : DecidableRel G.Adj), G.IsSRGWith 99 14 1 2 := by
  sorry
