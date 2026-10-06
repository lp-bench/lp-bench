import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Infix

namespace Pattern

variable {m : ℕ} {α : Type*}

/-- A pattern `p` — a word over the variables `Fin m` — *occurs* in the word `w` when
some non-erasing substitution of the variables by nonempty words turns `p` into a factor
of `w`. -/
def Occurs (p : List (Fin m)) (w : List α) : Prop :=
  ∃ h : Fin m → List α, (∀ x, h x ≠ []) ∧ p.flatMap h <:+: w

/-- The factor of the infinite word `w` of length `n` starting at position `i`. -/
def factor (w : ℕ → α) (i n : ℕ) : List α := List.ofFn fun j : Fin n => w (i + j)

/-- The infinite word `w` avoids the pattern `p`: `p` occurs in no factor of `w`. -/
def Avoids (p : List (Fin m)) (w : ℕ → α) : Prop := ∀ i n, ¬ Occurs p (factor w i n)

/-- `p` is `k`-avoidable: some infinite word over `k` letters avoids it. -/
def IsKAvoidable (p : List (Fin m)) (k : ℕ) : Prop := ∃ w : ℕ → Fin k, Avoids p w

/-- `p` is avoidable: it is `k`-avoidable for some `k`. -/
def IsAvoidable (p : List (Fin m)) : Prop := ∃ k, IsKAvoidable p k

end Pattern
