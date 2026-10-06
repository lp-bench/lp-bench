import Mathlib.Tactic

variable (𝔽 : Type) [Field 𝔽] (n : ℕ)

noncomputable section

namespace Hypermatrix

/-
A: tensor
n: dimension of A
m: rank of A
-/
def Tensor (m : ℕ) := Vector (Fin n) m → 𝔽

/-- Helper: Extract sub-vector -/
def subVector {α : Type} {n : ℕ} (v : Vector α n)
  (start len : ℕ) (h : start + len ≤ n) : Vector α len :=
  ⟨ v.toList.drop start |>.take len |>.toArray, by
    simp [List.length_take, List.length_drop]
    omega⟩

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

theorem P016 {m k l : ℕ}
  (hm : m ≥ 1) (hk : k ≥ 1) (hl : l ≥ 1)
  (A : Tensor 𝔽 n m) (B : Tensor 𝔽 n k) (C : Tensor 𝔽 n l) :
  (A ⊡ B) ⊡ C = cast (by grind) (A ⊡ (B ⊡ C)) := sorry

end Hypermatrix
