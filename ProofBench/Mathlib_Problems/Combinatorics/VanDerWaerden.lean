import Mathlib.Order.Lattice.Nat

namespace VanDerWaerden

/-- The colouring `C` has a monochromatic `m`-term arithmetic progression of colour `c` with
positive common difference inside `{0, …, n - 1}`. -/
def HasMonoAP {α : Type*} (C : ℕ → α) (c : α) (m n : ℕ) : Prop :=
  ∃ b d, 0 < d ∧ ∀ i < m, b + d * i < n ∧ C (b + d * i) = c

/-- The two-colour van der Waerden number `w(k, ℓ)`: the least `n` such that every red–blue
colouring of `{0, …, n - 1}` (red `true`, blue `false`) contains a red `k`-term or a blue
`ℓ`-term arithmetic progression. -/
noncomputable def mixedVdW (k ℓ : ℕ) : ℕ :=
  sInf {n | ∀ C : ℕ → Bool, HasMonoAP C true k n ∨ HasMonoAP C false ℓ n}

/-- Concavity of the van der Waerden numbers at `(k, ℓ)`: `w(k + 1, ℓ - 1) ≤ w(k, ℓ)`. -/
def VdWConcavity (k ℓ : ℕ) : Prop :=
  mixedVdW (k + 1) (ℓ - 1) ≤ mixedVdW k ℓ

end VanDerWaerden
