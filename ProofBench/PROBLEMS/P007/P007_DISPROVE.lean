/-
Prove-or-disprove companion — DISPROVE polarity for P007 (Sphere Packing,
universal lattice-optimality form).

`P007` (in `P007.lean`) and `P007_disprove` (below) form a polarity pair
in the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

A sorry-free proof of `P007_disprove` exhibits a dimension `d` in which no
lattice packing attains the sphere-packing constant — i.e. some packing is
strictly denser than every lattice packing of `ℝ^d`. This is widely believed to
occur in high dimensions but is unknown for any specific `d`, so the polarity is
genuinely open.

Evaluation note: a submitted proof of either polarity must be type-checked in
isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts as an
axiom).  Importing `P007.lean` here is sound — `¬P` is not derivable from the
axiom `P` — but harness-level isolation per target is still the safe protocol.
-/
import ProofBench.PROBLEMS.P007.P007

open MeasureTheory Metric Filter
open scoped ENNReal

/-- **Disprove version of P007.**  The negation of universal lattice optimality:
for some dimension `d`, the sphere-packing constant strictly exceeds the lattice
sphere-packing constant (no lattice packing is densest). -/
theorem P007_disprove :
    ¬ ∀ (d : ℕ), spherePackingConstant d = latticePackingConstant d := sorry
