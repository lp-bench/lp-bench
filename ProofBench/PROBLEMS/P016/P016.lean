import Mathlib.Tactic

variable (𝔽 : Type) [Field 𝔽] (n : ℕ)

noncomputable section

namespace Hypermatrix

/-- An order-`m` tensor of dimension `n` over `𝔽`: an entry in `𝔽` for each length-`m` vector
of indices in `Fin n`. -/
def Tensor (m : ℕ) := Vector (Fin n) m → 𝔽

/-- The sub-vector of `v` of length `len` starting at position `start`. -/
def subVector {α : Type} {n : ℕ} (v : Vector α n)
  (start len : ℕ) (h : start + len ≤ n) : Vector α len :=
  ⟨ v.toList.drop start |>.take len |>.toArray, by
    simp [List.length_take, List.length_drop]
    omega⟩

/-- The Shao product `A ⊡ B` of tensors of orders `m` and `k`, of order `(m - 1)(k - 1) + 1`:
its entry at `(i, α₁, …, α_{m-1})` is `∑ⱼ A(i, j₁, …, j_{m-1}) ∏ᵣ B(jᵣ, αᵣ)`, where the
`αᵣ` are the consecutive blocks of length `k - 1` of the index tail. -/
def shaoProduct {𝔽 : Type} [Field 𝔽]
    {m k : ℕ} (hm : m ≥ 1) (hk : k ≥ 1)
    (A : Tensor 𝔽 n m) (B : Tensor 𝔽 n k) :
    Tensor 𝔽 n ((m - 1) * (k - 1) + 1)  :=
  fun resultIdx =>
    let i := resultIdx.head
    let rest : Vector (Fin n) ((m - 1) * (k - 1)) := resultIdx.tail
    let getAlpha (r : Fin (m - 1)) : Vector (Fin n) (k - 1) :=
      subVector rest (r.val * (k - 1)) (k - 1)
        (by
          have hr : r.val < m - 1 := r.is_lt
          have : (r.val + 1) * (k - 1) ≤ (m - 1) * (k - 1) := by
            apply Nat.mul_le_mul_right (k - 1)
            exact Nat.succ_le_of_lt hr
          have h2 : r.val * (k - 1) + (k - 1) = (r.val + 1) * (k - 1) := by
            ring
          linarith [this, h2])
    ∑ js : Fin (m - 1) → Fin n,
      let aIndices := #[i] ++ (Array.ofFn (fun r => js r))
      let aVal := A ⟨aIndices, by simp [aIndices] ; omega⟩
      let bProd := ∏ r : Fin (m - 1),
        let j_r := js r
        let alpha := getAlpha r
        let bIndices := #[j_r] ++ alpha.toArray
        B ⟨bIndices, by grind⟩
      aVal * bProd

scoped infixl:70 " ⊡ " => shaoProduct _ (by omega) (by omega)

/-- Associativity of the Shao product (Shao 2013, Linear Algebra Appl.); both sides have
order `(m - 1)(k - 1)(l - 1) + 1` and are compared via `cast`. -/
theorem P016 {m k l : ℕ}
  (hm : m ≥ 1) (hk : k ≥ 1) (hl : l ≥ 1)
  (A : Tensor 𝔽 n m) (B : Tensor 𝔽 n k) (C : Tensor 𝔽 n l) :
  (A ⊡ B) ⊡ C = cast (by grind) (A ⊡ (B ⊡ C)) := sorry

end Hypermatrix
