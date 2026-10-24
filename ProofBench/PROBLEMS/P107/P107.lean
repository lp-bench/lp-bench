import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.RandomGraphs

open scoped BigOperators ENNReal
open Filter Topology

noncomputable section

namespace SpecifiedDegreeEmbedding

namespace DegreeSequence

/-- The entry `P(d)_ij` of Definition 1.6: `d_i d_j / (‖d‖₁ + d_i d_j)` for `i ≠ j`, and `0`
on the diagonal. -/
def edgeParameter {n : Nat} (d : DegreeSequence n) (i j : Fin n) : Real :=
  if i = j then 0
  else
    ((d.degree i : Real) * (d.degree j : Real)) /
      ((d.total : Real) +
        (d.degree i : Real) * (d.degree j : Real))

/-- The symmetric matrix `P(d)` from Definition 1.6. -/
def edgeMatrix {n : Nat} (d : DegreeSequence n) : Matrix (Fin n) (Fin n) Real :=
  fun i j => d.edgeParameter i j

/-- `P(d)` vanishes on the diagonal. -/
@[simp]
theorem edgeParameter_self {n : Nat} (d : DegreeSequence n) (i : Fin n) :
    d.edgeParameter i i = 0 := by
  simp [edgeParameter]

/-- `P(d)_ij = P(d)_ji`. -/
theorem edgeParameter_symm {n : Nat} (d : DegreeSequence n) (i j : Fin n) :
    d.edgeParameter i j = d.edgeParameter j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : Not (j = i) := fun h => hij h.symm
    simp [edgeParameter, hij, hji, mul_comm]

/-- `P(d)` is symmetric. -/
theorem edgeMatrix_transpose {n : Nat} (d : DegreeSequence n) :
    d.edgeMatrix.transpose = d.edgeMatrix := by
  ext i j
  exact d.edgeParameter_symm j i

/-- The diagonal entries of `P(d)` are `0`. -/
@[simp]
theorem edgeMatrix_apply_self {n : Nat} (d : DegreeSequence n) (i : Fin n) :
    d.edgeMatrix i i = 0 :=
  d.edgeParameter_self i

/-- The entries of `P(d)` are nonnegative. -/
theorem edgeParameter_nonnegative {n : Nat} (d : DegreeSequence n)
    (i j : Fin n) :
    0 <= d.edgeParameter i j := by
  by_cases hij : i = j
  · simp [edgeParameter, hij]
  · rw [edgeParameter, if_neg hij]
    positivity

/-- If the degree sequence has positive total degree, every off-diagonal
parameter is strictly below one. -/
theorem edgeParameter_lt_one {n : Nat} (d : DegreeSequence n)
    (htotal : 0 < d.total) {i j : Fin n} (hij : Not (i = j)) :
    d.edgeParameter i j < 1 := by
  rw [edgeParameter, if_neg hij]
  have htotalReal : (0 : Real) < d.total := by
    exact_mod_cast htotal
  apply (div_lt_one (by positivity)).2
  linarith

/-- If `‖d‖₁ > 0`, the entries of `P(d)` are at most `1`. -/
theorem edgeParameter_le_one {n : Nat} (d : DegreeSequence n)
    (htotal : 0 < d.total) (i j : Fin n) :
    d.edgeParameter i j <= 1 := by
  by_cases hij : i = j
  · simp [edgeParameter, hij]
  · exact (d.edgeParameter_lt_one htotal hij).le

/-- The map `f(x) = 1 - e^{-x}` of Theorem 1.8, applied entrywise to `P(d)`. -/
def poissonize (x : Real) : Real :=
  1 - Real.exp (-x)

/-- `f` maps `[0, ∞)` into `[0, 1)`. -/
theorem poissonize_mem_Ico {x : Real} (hx : 0 <= x) :
    poissonize x ∈ Set.Ico 0 1 := by
  constructor
  · rw [poissonize, sub_nonneg]
    simpa using (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))
  · have hexp : 0 < Real.exp (-x) := Real.exp_pos (-x)
    dsimp [poissonize]
    linarith

/-- `1 - e^{-x} <= x`: the Poissonized probabilities are at most the original ones. -/
theorem poissonize_le_self (x : Real) : poissonize x <= x := by
  have h := Real.add_one_le_exp (-x)
  dsimp [poissonize]
  linarith

/-- The entries of `f(P(d))` are probabilities. -/
theorem poissonize_edgeParameter_mem_Icc {n : Nat} (d : DegreeSequence n) (i j : Fin n) :
    poissonize (d.edgeParameter i j) ∈ Set.Icc (0 : Real) 1 :=
  let h := poissonize_mem_Ico (d.edgeParameter_nonnegative i j)
  ⟨h.1, h.2.le⟩

/-- `Δ(d) = max_i d_i` (and `0` on the empty vertex set). -/
def maxDegree {n : Nat} (d : DegreeSequence n) : Nat :=
  Finset.univ.sup d.degree

/-- `δ(d) = min_i d_i` (and `0` on the empty vertex set). -/
def minDegree {n : Nat} (d : DegreeSequence n) : Nat :=
  ⨅ i, d.degree i

/-- `J(d) = Σ_{i=1}^{d_1} d_i` for `d_1 >= d_2 >= … >= d_n`: the sum of the `Δ(d)` largest
degrees, i.e. the largest sum of `Δ(d)` distinct degrees (`Δ(d) <= n - 1` for a realisable
sequence; the size is capped at `n` for definiteness). -/
def topDegreeSum {n : Nat} (d : DegreeSequence n) : Nat :=
  (Finset.univ.powersetCard (min d.maxDegree n)).sup fun S => ∑ i ∈ S, d.degree i

/-- Every degree is at most `Δ(d)`. -/
theorem degree_le_maxDegree {n : Nat} (d : DegreeSequence n) (i : Fin n) :
    d.degree i <= d.maxDegree :=
  Finset.le_sup (f := d.degree) (Finset.mem_univ i)

/-- `J(d) <= Δ(d)²`, the observation by which the paper derives Theorem 1.7 from Theorem 1.8. -/
theorem topDegreeSum_le_sq {n : Nat} (d : DegreeSequence n) :
    d.topDegreeSum <= d.maxDegree * d.maxDegree := by
  unfold topDegreeSum
  refine Finset.sup_le fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  calc ∑ i ∈ S, d.degree i <= S.card • d.maxDegree :=
        S.sum_le_card_nsmul _ _ fun i _ => d.degree_le_maxDegree i
    _ = S.card * d.maxDegree := smul_eq_mul _ _
    _ <= d.maxDegree * d.maxDegree := by
        rw [hS.2]
        exact Nat.mul_le_mul_right _ (min_le_left _ _)

end DegreeSequence

open DegreeSequence

/-- Theorem 1.8 of Gao–Ohapkin, arXiv:2302.09729.  If the degree sequences `d(n)` are realisable,
`J(d) = o(‖d‖₁)` and `δ(d) ≫ log n`, there are `ε(n) ∈ [0, 1]` with `ε → 0` and couplings
`(G_L, G)` of `G(n, (1 - ε) f(P(d)))` and `G(n, d)` with `P(G_L ⊆ G) → 1`. -/
theorem P107 (d : forall n : Nat, DegreeSequence n)
    (hgraph : forall n, (d n).IsGraphical)
    (hJ : Tendsto (fun n => ((d n).topDegreeSum : Real) / ((d n).total : Real)) atTop (𝓝 0))
    (hδ : Tendsto (fun n => ((d n).minDegree : Real) / Real.log (n : Real)) atTop atTop) :
    ∃ ε : Nat -> Real, (forall n, ε n ∈ Set.Icc (0 : Real) 1) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ κ : forall n, Coupling
          (independentEdgeGraph n ((1 - ε n) • (d n).edgeMatrix.map poissonize))
          (uniformDegreeGraph n (d n)),
        Tendsto (fun n => (κ n).embedProb) atTop (𝓝 1) := by
  sorry

/-- Theorem 1.8 in the form used for its applications: for every confidence level `q < 1`, the
coupling embeds `G(n, W)` into `G(n, d)` with probability more than `q` for all large `n`. -/
theorem embedding_theorem_eventually (d : forall n : Nat, DegreeSequence n)
    (hgraph : forall n, (d n).IsGraphical)
    (hJ : Tendsto (fun n => ((d n).topDegreeSum : Real) / ((d n).total : Real)) atTop (𝓝 0))
    (hδ : Tendsto (fun n => ((d n).minDegree : Real) / Real.log (n : Real)) atTop atTop) :
    ∃ ε : Nat -> Real, (forall n, ε n ∈ Set.Icc (0 : Real) 1) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ κ : forall n, Coupling
          (independentEdgeGraph n ((1 - ε n) • (d n).edgeMatrix.map poissonize))
          (uniformDegreeGraph n (d n)),
        forall q : ℝ≥0∞, q < 1 -> ∀ᶠ n in atTop, q < (κ n).embedProb := by
  obtain ⟨ε, hε, hε0, κ, hκ⟩ := P107 d hgraph hJ hδ
  exact ⟨ε, hε, hε0, κ, fun q hq => (tendsto_order.1 hκ).1 q hq⟩

/-- The matrix `W` of Theorem 1.8 is dominated by `f(P(d))`, which is dominated by `P(d)`:
the embedded random graph is sparser than `G(n, P(d))`, the model with the matrix of
Definition 1.6 (asymptotically the Chung-Lu model when `Δ(d)² = o(‖d‖₁)`, Section 1.1). -/
theorem smul_poissonize_le_edgeMatrix {n : Nat} (d : DegreeSequence n) {ε : Real}
    (hε : ε ∈ Set.Icc (0 : Real) 1) (i j : Fin n) :
    ((1 - ε) • d.edgeMatrix.map poissonize) i j <= d.edgeMatrix i j := by
  rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have h0 : 0 <= poissonize (d.edgeMatrix i j) :=
    (poissonize_edgeParameter_mem_Icc d i j).1
  calc (1 - ε) * poissonize (d.edgeMatrix i j) <= 1 * poissonize (d.edgeMatrix i j) :=
        mul_le_mul_of_nonneg_right (by linarith [hε.1]) h0
    _ = poissonize (d.edgeMatrix i j) := one_mul _
    _ <= d.edgeMatrix i j := poissonize_le_self _

end SpecifiedDegreeEmbedding
