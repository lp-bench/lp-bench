import Mathlib.Data.Finset.Defs
import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.Basic

universe u

/-!
# Ryser's Hypergraph Conjecture
-/

open Finset

/- Ryser's hypergraph conjecture: in every `r`-partite `r`-uniform hypergraph
with `r ≥ 2`, the cover number is at most `(r - 1)` times the matching
number. -/
def RyserConjecture : Prop :=
  ∀ r : ℕ, 2 ≤ r →
  ∀ {V : Type u} [DecidableEq V] (H : Hypergraph V),
  H.IsUniform r → H.IsPartite r →
    H.coverNumber ≤ (r - 1) * H.matchingNumber

/-- **Refuting Ryser's hypergraph conjecture.**  The conjecture is a theorem
for `r = 2` (König) and `r = 3` (Aharoni) and was disproved for large `r` in
October 2026 (OpenAI math release, Lean-checked).  Show that `RyserConjecture`
fails: some `r ≥ 2` and some `r`-partite `r`-uniform hypergraph have cover
number exceeding `(r - 1)` times the matching number. -/
theorem P008 : ¬ RyserConjecture.{u} := sorry
