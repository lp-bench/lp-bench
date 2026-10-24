import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

namespace SparseRandomMatrixFullRank

/-- An `m` by `n` matrix has full row rank when every right-hand side in `F^m` is a
matrix-vector product `A x`, i.e. every linear system `A x = y` is solvable. -/
def HasFullRowRank {F m n : Type*} [Field F] [Fintype n]
    (A : Matrix m n F) : Prop :=
  Function.Surjective A.mulVec

/-- Solvability of the linear system `A x = y`. -/
def LinearSystemSolvable {F m n : Type*} [Field F] [Fintype n]
    (A : Matrix m n F) (y : m -> F) : Prop :=
  Exists fun x : n -> F => A.mulVec x = y

/-- Full row rank means that every linear system `A x = y` is solvable. -/
theorem hasFullRowRank_iff_all_systems_solvable
    {F m n : Type*} [Field F] [Fintype n] (A : Matrix m n F) :
    HasFullRowRank A <-> forall y : m -> F, LinearSystemSolvable A y := by
  constructor
  · intro h y
    exact h y
  · intro h y
    exact h y

/-- A rectangular matrix has a right inverse when multiplication on the right
produces the identity matrix on its row index. -/
def HasRightInverse {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    [DecidableEq m] (A : Matrix m n F) : Prop :=
  Exists fun B : Matrix n m F => A * B = 1

/-- A right inverse supplies a solution to every linear system. -/
theorem hasFullRowRank_of_hasRightInverse
    {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    [DecidableEq m] (A : Matrix m n F) (hA : HasRightInverse A) :
    HasFullRowRank A := by
  rcases hA with ⟨B, hAB⟩
  intro y
  refine Exists.intro (B.mulVec y) ?_
  calc
    A.mulVec (B.mulVec y) = (A * B).mulVec y :=
      Matrix.mulVec_mulVec y A B
    _ = (1 : Matrix m m F).mulVec y := by rw [hAB]
    _ = y := Matrix.one_mulVec y

/-- Full row rank agrees with Mathlib's numerical matrix rank. -/
theorem hasFullRowRank_iff_rank_eq_card_rows
    {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (A : Matrix m n F) :
    HasFullRowRank A <-> A.rank = Fintype.card m := by
  change Function.Surjective A.mulVecLin <-> _
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h
    change Module.finrank F A.mulVecLin.range = Fintype.card m
    rw [h, finrank_top, Module.finrank_fintype_fun_eq_card]
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using h

/-- Mathlib row independence implies the usual numerical full-rank equation. -/
theorem rank_eq_card_rows_of_linearIndependent
    {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    {A : Matrix m n F} (hA : LinearIndependent F A.row) :
    A.rank = Fintype.card m :=
  hA.rank_matrix

/-- The subspace of solvable right-hand sides: the image of `A`. -/
def SolvableRightHandSideSpace
    {F m n : Type*} [Field F] [Fintype n] (A : Matrix m n F) :
    Submodule F (m -> F) :=
  A.mulVecLin.range

/-- `y` lies in the image of `A` exactly when `A x = y` is solvable. -/
theorem mem_solvableRightHandSideSpace_iff
    {F m n : Type*} [Field F] [Fintype n]
    (A : Matrix m n F) (y : m -> F) :
    (SolvableRightHandSideSpace A).carrier y <->
      LinearSystemSolvable A y := by
  rfl

/-- Over a finite field, the number of solvable right-hand sides is the field
order raised to the matrix rank. -/
theorem card_solvableRightHandSideSpace
    {F m n : Type*} [Field F] [Fintype F] [Fintype m] [Fintype n]
    (A : Matrix m n F) :
    Nat.card (SolvableRightHandSideSpace A) = Nat.card F ^ A.rank := by
  rw [Module.natCard_eq_pow_finrank
    (K := F) (V := SolvableRightHandSideSpace A)]
  rfl

/-- If `A` does not have full row rank, at most a fraction `1 / |F|` of the right-hand sides
are solvable. -/
theorem card_solvableRightHandSideSpace_mul_fieldOrder_le
    {F m n : Type*} [Field F] [Fintype F] [Fintype m] [Fintype n]
    (A : Matrix m n F) (hA : Not (HasFullRowRank A)) :
    Nat.card (SolvableRightHandSideSpace A) * Nat.card F <=
      Nat.card (m -> F) := by
  have hrank_ne : Not (A.rank = Fintype.card m) := by
    intro hrank
    exact hA ((hasFullRowRank_iff_rank_eq_card_rows A).2 hrank)
  have hrank_lt : A.rank < Fintype.card m :=
    lt_of_le_of_ne A.rank_le_card_height hrank_ne
  rw [card_solvableRightHandSideSpace,
    Module.natCard_eq_pow_finrank (K := F) (V := m -> F),
    Module.finrank_fintype_fun_eq_card]
  calc
    Nat.card F ^ A.rank * Nat.card F =
        Nat.card F ^ (A.rank + 1) := by rw [pow_succ]
    _ <= Nat.card F ^ Fintype.card m :=
      pow_le_pow_right' Nat.card_pos (Nat.succ_le_iff.mpr hrank_lt)

/-- A probability distribution on `ℕ` (a degree law), given by real masses, with finite
second moment; the paper's `2 + η` moment condition is a hypothesis of the theorem. -/
structure NatLaw where
  mass : Nat -> Real
  mass_nonnegative : forall r, 0 <= mass r
  summable_mass : Summable mass
  total_mass : tsum mass = 1
  summable_second_moment :
    Summable fun r => mass r * (r : Real) ^ 2

namespace NatLaw

/-- The probability generating function `E[z^X]`. -/
def pgf (X : NatLaw) (z : Real) : Real :=
  tsum fun r => X.mass r * z ^ r

/-- The termwise derivative `∑ (r + 1) P(X = r + 1) z^r` of the probability generating
function. -/
def pgfDeriv (X : NatLaw) (z : Real) : Real :=
  tsum fun r => X.mass (r + 1) * (r + 1 : Real) * z ^ r

/-- The first moment `E[X]`. -/
def mean (X : NatLaw) : Real :=
  tsum fun r => X.mass r * r

/-- `g` is the greatest common divisor of the (possibly infinite) support of `X`. -/
def IsSupportGCD (X : NatLaw) (g : Nat) : Prop :=
  0 < g /\
    (forall r, X.mass r != 0 -> Dvd.dvd g r) /\
    forall c, 0 < c ->
      (forall r, X.mass r != 0 -> Dvd.dvd c r) -> Dvd.dvd c g

/-- The distribution is supported on natural numbers at least `lower`. -/
def SupportedAtLeast (X : NatLaw) (lower : Nat) : Prop :=
  forall r, X.mass r != 0 -> lower <= r

end NatLaw

/-- The degree laws of Theorem 1.1: `variableDegree` is the paper's `d` (column degrees,
with support gcd `𝔡`) and `checkDegree` is its `k` (row degrees, supported on `k ≥ 3`). -/
structure DegreeParameters where
  variableDegree : NatLaw
  checkDegree : NatLaw
  variableSupportGCD : Nat
  isVariableSupportGCD :
    variableDegree.IsSupportGCD variableSupportGCD
  checkDegreeAtLeastThree : checkDegree.SupportedAtLeast 3
  checkMeanPositive : 0 < checkDegree.mean

namespace DegreeParameters

/-- The function `Phi` from equation (1.2) of the paper. -/
def phi (P : DegreeParameters) (z : Real) : Real :=
  P.variableDegree.pgf
      (1 - P.checkDegree.pgfDeriv z / P.checkDegree.mean) -
    P.variableDegree.mean / P.checkDegree.mean *
      (1 - P.checkDegree.pgf z -
        (1 - z) * P.checkDegree.pgfDeriv z)

/-- The strict full-rank condition (1.3): zero is the unique maximizer of
`Phi` on `[0,1]`. -/
def StrictPhiCondition (P : DegreeParameters) : Prop :=
  forall z : Real, 0 < z -> z <= 1 -> P.phi z < P.phi 0

end DegreeParameters

/-- A matrix over `F` with `n` columns; the number of rows is random, so it is part of the
sample. -/
structure MatrixSample (F : Type*) (n : Nat) where
  rowCount : Nat
  matrix : Matrix (Fin rowCount) (Fin n) F

instance matrixSampleMeasurableSpace (F : Type*) (n : Nat) :
    MeasurableSpace (MatrixSample F n) := Top.top

/-- The event that a sampled matrix has full row rank. -/
def FullRowRankEvent {F : Type*} [Field F] {n : Nat}
    (sample : MatrixSample F n) : Prop :=
  HasFullRowRank sample.matrix

/-- A sequence of events occurs with high probability (a.a.s.) when its probability tends
to one. -/
def AsymptoticallyAlmostSurely (probability : Nat -> Real) : Prop :=
  Tendsto probability atTop (nhds 1)

/-- Probability of the full-row-rank event under a law on matrix samples. -/
def fullRowRankProbability {F : Type*} [Field F] {n : Nat}
    (mu : Measure (MatrixSample F n)) : Real :=
  mu.real {sample | FullRowRankEvent sample}

/-- A sequence of matrix laws has full row rank with high probability. -/
def FullRowRankWithHighProbability {F : Type*} [Field F]
    (law : forall n : Nat, Measure (MatrixSample F n)) : Prop :=
  AsymptoticallyAlmostSurely fun n => fullRowRankProbability (law n)

/-- `AsymptoticallyAlmostSurely` depends only on the values of the probabilities. -/
theorem asymptoticallyAlmostSurely_congr
    {p q : Nat -> Real} (h : forall n, p n = q n) :
    AsymptoticallyAlmostSurely p <-> AsymptoticallyAlmostSurely q := by
  cases funext h
  rfl

/-- If `s n ≤ r n + c (1 - r n)` with `c < 1`, `r n ≤ 1` and `s n → 1`, then `r n → 1`
(`r`: probability of full row rank, `s`: probability that a random right-hand side is
solvable). -/
theorem tendsto_one_of_solvability_gap
    (c : Real) (hc : c < 1)
    (rankProbability solvabilityProbability : Nat -> Real)
    (hrank_le_one : forall n, rankProbability n <= 1)
    (hcomparison : forall n,
      solvabilityProbability n <=
        rankProbability n + c * (1 - rankProbability n))
    (hsolvable : Tendsto solvabilityProbability atTop (nhds 1)) :
    Tendsto rankProbability atTop (nhds 1) := by
  let lower : Nat -> Real := fun n =>
    (solvabilityProbability n - c) / (1 - c)
  have hcpos : 0 < 1 - c := sub_pos.mpr hc
  have hcne : Not (1 - c = 0) := ne_of_gt hcpos
  have hc_tendsto : Tendsto (fun _ : Nat => c) atTop (nhds c) :=
    tendsto_const_nhds
  have hlower : Tendsto lower atTop (nhds 1) := by
    simpa [lower, hcne] using
      (hsolvable.sub hc_tendsto).div_const (1 - c)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds
  · intro n
    dsimp [lower]
    apply (div_le_iff₀ hcpos).2
    nlinarith [hcomparison n]
  · exact hrank_le_one

/-- The case `c = 1 / q` of `tendsto_one_of_solvability_gap`, for `q > 1`. -/
theorem tendsto_one_of_finiteField_solvability_gap
    (q : Nat) (hq : 1 < q)
    (rankProbability solvabilityProbability : Nat -> Real)
    (hrank_le_one : forall n, rankProbability n <= 1)
    (hcomparison : forall n,
      solvabilityProbability n <=
        rankProbability n + (1 - rankProbability n) / (q : Real))
    (hsolvable : Tendsto solvabilityProbability atTop (nhds 1)) :
    Tendsto rankProbability atTop (nhds 1) := by
  apply tendsto_one_of_solvability_gap (1 / (q : Real))
  · apply (div_lt_one (by positivity : (0 : Real) < q)).2
    exact_mod_cast hq
  · exact hrank_le_one
  · intro n
    simpa [div_eq_mul_inv, mul_comm] using hcomparison n
  · exact hsolvable

/-- The side condition of Theorem 1.1: the order `q = |F|` of the finite field is coprime
to the gcd `𝔡` of the support of `d`. -/
def FieldOrderCoprime {F : Type*} [Fintype F]
    (P : DegreeParameters) : Prop :=
  Nat.Coprime (Fintype.card F) P.variableSupportGCD

/-- `n` independent copies of a law, as a law on `Fin n -> α`: the copies are
drawn one after the other. -/
def piLaw {α : Type*} (X : PMF α) : forall n : Nat, PMF (Fin n -> α)
  | 0 => PMF.pure fun i => i.elim0
  | n + 1 => X.bind fun x => (piLaw X n).map (Fin.cons x)

/-- The probability mass function of a `NatLaw`. -/
def NatLaw.toPMF (X : NatLaw) : PMF Nat := by
  refine ⟨fun r => ENNReal.ofReal (X.mass r), ?_⟩
  have h1 : HasSum X.mass 1 := X.total_mass ▸ X.summable_mass.hasSum
  apply ENNReal.hasSum_coe.mpr
  rw [← Real.toNNReal_one]
  exact h1.toNNReal X.mass_nonnegative

/-- The Poisson law `Po(r)`. -/
def poissonLaw (r : NNReal) : PMF Nat :=
  (ProbabilityTheory.poissonMeasure r).toPMF

/-- The degree data of Section 1.2.1: the variable degrees `d_1, …, d_n`, the
row count `m` and the check degrees `k_1, …, k_m`. -/
structure DegreeProfile (n : Nat) where
  rowCount : Nat
  variableDegrees : Fin n -> Nat
  checkDegrees : Fin rowCount -> Nat

/-- The unconditioned law of the degree data: independent variable degrees with
law `d`, an independent row count `m ~ Po(E[d] n / E[k])`, and independent check
degrees with law `k`. -/
def degreeProfileLaw (P : DegreeParameters) (n : Nat) : PMF (DegreeProfile n) :=
  (piLaw P.variableDegree.toPMF n).bind fun d =>
    (poissonLaw
      (Real.toNNReal (P.variableDegree.mean * n / P.checkDegree.mean))).bind fun m =>
      (piLaw P.checkDegree.toPMF m).map fun k => ⟨m, d, k⟩

/-- The biadjacency matrices of the simple bipartite graphs with the prescribed
degrees: row `i` (check node `a_i`) has `k_i` ones and column `j` (variable node
`x_j`) has `d_j` ones. -/
def bipartiteGraphsWithDegrees {n : Nat} (D : DegreeProfile n) :
    Finset (Fin D.rowCount -> Fin n -> Bool) :=
  Finset.univ.filter fun B =>
    (forall i, (Finset.univ.filter fun j => B i j = true).card = D.checkDegrees i) /\
    (forall j, (Finset.univ.filter fun i => B i j = true).card = D.variableDegrees j)

/-- The conditioning event of Section 1.2.1: the degree sums agree (1.1) and a
simple bipartite graph with these degrees exists. -/
def DegreeProfile.Admissible {n : Nat} (D : DegreeProfile n) : Prop :=
  (∑ j, D.variableDegrees j = ∑ i, D.checkDegrees i) /\
    (bipartiteGraphsWithDegrees D).Nonempty

open scoped Classical in
/-- The degree data conditioned on admissibility; if admissibility has probability zero,
the unconditioned law is the junk value. -/
def conditionedProfileLaw (P : DegreeParameters) (n : Nat) : PMF (DegreeProfile n) :=
  if h : ∃ D ∈ {D : DegreeProfile n | D.Admissible}, D ∈ (degreeProfileLaw P n).support then
    (degreeProfileLaw P n).filter {D | D.Admissible} h
  else degreeProfileLaw P n

open scoped Classical in
/-- A uniformly random simple bipartite graph with the prescribed degrees, the
graph `𝔾_n(d, k)` of Section 1.2.1, as a biadjacency matrix; the empty graph is
the junk value when no such graph exists. -/
def uniformBipartiteGraph {n : Nat} (D : DegreeProfile n) :
    PMF (Fin D.rowCount -> Fin n -> Bool) :=
  if h : (bipartiteGraphsWithDegrees D).Nonempty then PMF.uniformOfFinset _ h
  else PMF.pure fun _ _ => false

/-- A Tanner graph: the biadjacency matrix of a bipartite graph with `m` check
nodes and `n` variable nodes. -/
structure TannerGraph (n : Nat) where
  rowCount : Nat
  adj : Fin rowCount -> Fin n -> Bool

/-- The law of the random Tanner graph `𝔾 = 𝔾_n(d, k)` of Section 1.2.1. -/
def tannerGraphLaw (P : DegreeParameters) (n : Nat) : PMF (TannerGraph n) :=
  (conditionedProfileLaw P n).bind fun D =>
    (uniformBipartiteGraph D).map fun B => ⟨D.rowCount, B⟩

/-- Independent coefficients with law `χ` on the edges of a Tanner graph: the
matrix `𝔸_{ij} = χ_{ij} 𝟙{a_i x_j ∈ E(𝔾)}`. -/
def coefficientMatrix {F : Type*} [Zero F] (χ : PMF F) {n : Nat} (G : TannerGraph n) :
    PMF (MatrixSample F n) :=
  (piLaw (piLaw χ n) G.rowCount).map fun c =>
    ⟨G.rowCount, Matrix.of fun i j => if G.adj i j then c i j else 0⟩

/-- The law of the random matrix `𝔸 = 𝔸_n(d, k, χ)` of Section 1.2.1, for a law `χ` of the
nonzero coefficients; `χ = 1` gives the zero-one biadjacency matrix. -/
def randomMatrixLaw (F : Type*) [Zero F] (P : DegreeParameters) (χ : PMF F) (n : Nat) :
    PMF (MatrixSample F n) :=
  (tannerGraphLaw P n).bind (coefficientMatrix χ)

/-- **Theorem 1.1** of Coja-Oghlan–Gao–Hahn-Klimroth–Lee–Müller–Rolvien, arXiv:2112.14090:
if `E[d^{2+η}], E[k^{2+η}] < ∞`, `q = |F|` is coprime to `𝔡`, `χ` lives on `F ∖ {0}` and
`Φ(z) < Φ(0)` for `0 < z ≤ 1`, then `𝔸_n(d, k, χ)` has full row rank over `F` with high
probability as `n → ∞` along the multiples of the support gcd `𝔨` of `k`. -/
theorem P102 (F : Type*) [Field F] [Fintype F]
    (P : DegreeParameters) (χ : PMF F) (hχ : ∀ x ∈ χ.support, x ≠ 0)
    (η : Real) (hη : 0 < η)
    (hmoment_d : Summable fun r => P.variableDegree.mass r * (r : Real) ^ (2 + η))
    (hmoment_k : Summable fun r => P.checkDegree.mass r * (r : Real) ^ (2 + η))
    (kgcd : Nat) (hkgcd : P.checkDegree.IsSupportGCD kgcd)
    (hcoprime : FieldOrderCoprime (F := F) P) (hphi : P.StrictPhiCondition) :
    AsymptoticallyAlmostSurely fun t =>
      fullRowRankProbability (randomMatrixLaw F P χ (kgcd * t)).toMeasure := by
  sorry

/-- **Theorem 1.1 for the zero-one matrix** `χ = 1`: the biadjacency matrix of
the random Tanner graph, read over `F`, has full row rank with high
probability. -/
theorem full_row_rank_theorem_of_const (F : Type*) [Field F] [Fintype F]
    (P : DegreeParameters) (η : Real) (hη : 0 < η)
    (hmoment_d : Summable fun r => P.variableDegree.mass r * (r : Real) ^ (2 + η))
    (hmoment_k : Summable fun r => P.checkDegree.mass r * (r : Real) ^ (2 + η))
    (kgcd : Nat) (hkgcd : P.checkDegree.IsSupportGCD kgcd)
    (hcoprime : FieldOrderCoprime (F := F) P) (hphi : P.StrictPhiCondition) :
    AsymptoticallyAlmostSurely fun t =>
      fullRowRankProbability (randomMatrixLaw F P (PMF.pure 1) (kgcd * t)).toMeasure := by
  refine P102 F P (PMF.pure 1) ?_ η hη hmoment_d hmoment_k kgcd hkgcd
    hcoprime hphi
  intro x hx
  rw [PMF.support_pure, Set.mem_singleton_iff] at hx
  rw [hx]
  exact one_ne_zero

end SparseRandomMatrixFullRank
