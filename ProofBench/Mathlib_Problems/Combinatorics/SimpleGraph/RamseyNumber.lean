import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Clique

open Filter Topology Asymptotics Real

variable {f : ℕ → ℝ} {c : ℝ}

/-- The normalized `t`-th root `f(t)^{1/t}` of a sequence. -/
noncomputable def seqRoot (f : ℕ → ℝ) (t : ℕ) : ℝ := (f t) ^ ((t : ℝ)⁻¹)

/-- The eventual **ε-bracket** predicate: for every `0 < ε < c`, the sequence is
eventually trapped in `[(c-ε)^t, (c+ε)^t]`. -/
def RootBracket (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < c → ∀ᶠ t in atTop, (c - ε) ^ t ≤ f t ∧ f t ≤ (c + ε) ^ t

/-- The diagonal Ramsey number `R(t)`: the least `n` such that every simple graph on `n` vertices
contains a clique of size `t` or an independent set of size `t`. -/
noncomputable def ramseyNumber (t : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (G : SimpleGraph (Fin n)),
    (∃ s : Finset (Fin n), G.IsNClique t s) ∨
    (∃ s : Finset (Fin n), (Gᶜ).IsNClique t s)}

/-- The normalized Ramsey sequence `t ↦ R(t)^{1/t}` whose convergence is the
famous open problem of Erdős. -/
noncomputable def ramseyRoot (t : ℕ) : ℝ := (ramseyNumber t : ℝ) ^ ((t : ℝ)⁻¹)

/-- **The Erdős limit conjecture**, in root-convergence form: `R(t)^{1/t}` converges to some
`c ∈ [√2, 4]`. Existence of the limit is open. -/
def RamseyLimitConjecture : Prop :=
  ∃ c, √2 ≤ c ∧ c ≤ 4 ∧ Tendsto ramseyRoot atTop (𝓝 c)
