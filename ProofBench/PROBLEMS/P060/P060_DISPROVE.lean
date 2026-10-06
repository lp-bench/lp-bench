/-
Prove-or-disprove companion — DISPROVE polarity for P060 (Chvátal's
toughness conjecture: some fixed toughness forces Hamiltonicity).

`P060` (in `P060.lean`) and `P060_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The conjecture is OPEN, and this polarity's truth value is genuinely
unknown.  A disproof must, for EVERY `t > 0`, produce a `t`-tough
non-Hamiltonian graph on at least three vertices.  The state of the art is
Bauer–Broersma–Veldman (2000): `(9/4 − ε)`-tough non-Hamiltonian graphs for
every `ε > 0`, built by joining copies of a gadget over a complete core;
a disproof would need such constructions with toughness growing without
bound, which the community considers unlikely — the conjecture is widely
believed, with `t = 3` a natural candidate.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Toughness

open SimpleGraph

universe u

/-- Disproof polarity of Chvátal's toughness conjecture: for every positive
`t` there is a `t`-tough non-Hamiltonian graph on at least three
vertices. -/
theorem P060_disprove :
    ¬ ∃ t : ℝ, 0 < t ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        3 ≤ Fintype.card V → G.IsTough t → G.IsHamiltonian := by
  sorry
