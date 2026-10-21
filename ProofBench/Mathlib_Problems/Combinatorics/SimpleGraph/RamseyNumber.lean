import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Clique

open Filter Topology Asymptotics Real

variable {f : ℕ → ℝ} {c : ℝ}

/-- The normalized `t`-th root `f(t)^{1/t}` of a sequence. -/
noncomputable def seqRoot (f : ℕ → ℝ) (t : ℕ) : ℝ := (f t) ^ ((t : ℝ)⁻¹)

/-- The eventual **ε-bracket** predicate: for every `0 < ε < c`, the sequence is
eventually trapped in `[(c-ε)^t, (c+ε)^t]`.  This is the "third conjecture" form. -/
def RootBracket (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < c → ∀ᶠ t in atTop, (c - ε) ^ t ≤ f t ∧ f t ≤ (c + ε) ^ t

/-! ## Ramsey specializations (reusing `ramseyRoot`, `RamseyLimitConjecture`) -/

noncomputable def ramseyNumber (t : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (G : SimpleGraph (Fin n)),
    (∃ s : Finset (Fin n), G.IsNClique t s) ∨
    (∃ s : Finset (Fin n), (Gᶜ).IsNClique t s)}

/-- The normalized Ramsey sequence `t ↦ R(t)^{1/t}` whose convergence is the
famous open problem of Erdős. -/
noncomputable def ramseyRoot (t : ℕ) : ℝ := (ramseyNumber t : ℝ) ^ ((t : ℝ)⁻¹)

/-- **The Erdős limit conjecture**, in root-convergence form:
some `c ∈ [√2, 4]` is the limit of `R(t)^{1/t}`.  Shared conjecture used by the
P116 upper bound; equivalent to the ε-bracket form via
`ramsey_rootBracket_iff_tendsto`.  Existence of the limit is the open Erdős
problem (and any such `c` is known to be `< 4`). -/
def RamseyLimitConjecture : Prop :=
  ∃ c, √2 ≤ c ∧ c ≤ 4 ∧ Tendsto ramseyRoot atTop (𝓝 c)
