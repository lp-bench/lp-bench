import Mathlib.Data.Matrix.Basic

open Finset Equiv Function

variable {G S : Type*} (M : Matrix S S S) (σ τ : Perm S)

/-- A Latin square is a matrix with entries in `S`,
whose rows and columns are indexed by `S` so that
no row or column contains the same entry more than once. -/
def IsLatinSq : Prop :=
  (∀ r, Injective (M r ·)) ∧
  (∀ c, Injective (M · c))

/-- `cells` is a partial transversal of `M`: its cells lie in distinct rows and distinct
columns and carry distinct symbols. -/
structure IsPT (cells : Finset (S × S)) where
  row_cond : Set.InjOn Prod.fst (cells : Set (S × S))
  col_cond : Set.InjOn Prod.snd (cells : Set (S × S))
  sym_cond : Set.InjOn (fun c => M c.1 c.2) (cells : Set (S × S))

variable [Fintype S]

/-- **Koksma's theorem** (Koksma 1969): every Latin square of size `n ≥ 7` has a partial
transversal of size at least `(2n + 1) / 3`, i.e. of size `T` with `3T ≥ 2n + 1`. -/
theorem P012 {hM : IsLatinSq M}
   {hN : Fintype.card S ≥ 7} :
    ∃ pt, IsPT M pt ∧ 3 * #pt ≥ 2 * (Fintype.card S) + 1 := sorry
