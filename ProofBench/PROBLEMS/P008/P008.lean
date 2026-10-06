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

theorem P008 : RyserConjecture := sorry
