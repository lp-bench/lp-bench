import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn

/-- A word over the alphabet `Fin n` is a *superpermutation* when every permutation of
`Fin n`, read as the word `σ 0, σ 1, …, σ (n - 1)`, occurs in it as a contiguous factor. -/
def IsSuperpermutation (n : ℕ) (w : List (Fin n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), List.ofFn σ <:+: w
