import Mathlib.Data.Finset.Defs
import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.Basic

universe u

open Finset

/-- Ryser's hypergraph conjecture: in every `r`-partite `r`-uniform hypergraph
with `r ≥ 2`, the cover number is at most `(r - 1)` times the matching
number. -/
def RyserConjecture : Prop :=
  ∀ r : ℕ, 2 ≤ r →
  ∀ {V : Type u} [DecidableEq V] (H : FinHypergraph V),
  H.IsUniform r → H.IsPartite r →
    H.coverNumber ≤ (r - 1) * H.matchingNumber

/-- **Refuting Ryser's hypergraph conjecture** (true for `r = 2` by König and `r = 3` by
Aharoni; disproved in OpenAI's math release, October 2026): for some `r ≥ 2`, some
`r`-partite `r`-uniform hypergraph has cover number larger than `(r - 1)` times its
matching number. -/
theorem P008 : ¬ RyserConjecture.{u} := sorry
