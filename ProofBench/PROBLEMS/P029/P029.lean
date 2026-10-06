import ProofBench.Mathlib_Problems.Combinatorics.Hypergraph.RangeCapturing

/- ==============================================================================
P029 — The reduction lemma for polychromatic colorings of geometric hypergraphs
(Planken & Ueckerdt, arXiv:2310.19982; Keszegh–Pálvölgyi, Lemma 3).

Shared definitions (the range-capturing hypergraph `H(V,R,m)`, polychromatic
colorings, shallow hitting sets, shrinkability, `m_R(k)`, the geometric range
families) live in `ProofBench.Mathlib.Combinatorics.Hypergraph.RangeCapturing`
and are imported above.  This sheet states the difficult result: for a
*shrinkable* range family, uniform `t`-shallow hitting sets yield the linear
polychromatic bound `m_R(k) ≤ t·(k-1)+1`.
============================================================================== -/

open Finset

namespace RangeCapturing

variable {d : ℕ}

/- **Lemma 3 (Keszegh and Pálvölgyi).**  For a *shrinkable* range family `R`,
if there is a constant `t ≥ 1` such that for every uniformity `m ≥ 1` every
`H(V, R, m)` admits a `t`-shallow hitting set, then `m_R(k) ≤ t·(k-1)+1 = O(k)`. -/
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
