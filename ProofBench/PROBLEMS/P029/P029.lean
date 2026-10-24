import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

open Finset

namespace RangeCapturing

variable {d : ℕ}

/-- Lemma 3 of Keszegh–Pálvölgyi (2019), as presented in Planken–Ueckerdt, arXiv:2310.19982:
if a shrinkable range family `R` has `t`-shallow hitting sets at every uniformity `m ≥ 1`,
then `H(V, R, t·(k-1)+1)` admits a polychromatic `k`-colouring for every finite `V` in
general position. -/
theorem P029
    (ranges : RangeFamily d) (t k : ℕ) (hk : 1 ≤ k)
    (hshrink : Shrinkable ranges)
    (hshallow : ∀ m : ℕ, 1 ≤ m → HasUniformShallowHittingSets ranges m t) :
    PolychromaticBound ranges k (t * (k - 1) + 1) := by
  sorry

/-- The `m_R(k) ≤ t·(k-1)+1` form of Lemma 3, via `polychromaticParameter`. -/
theorem lemma3_polychromaticParameter_le
    (ranges : RangeFamily d) (t k : ℕ) (hk : 1 ≤ k)
    (hshrink : Shrinkable ranges)
    (hshallow : ∀ m : ℕ, 1 ≤ m → HasUniformShallowHittingSets ranges m t) :
    polychromaticParameter ranges k ≤ t * (k - 1) + 1 :=
  Nat.sInf_le (P029 ranges t k hk hshrink hshallow)

end RangeCapturing
