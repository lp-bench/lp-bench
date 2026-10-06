import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# P045: The full rank condition for sparse random matrices

This file formalizes the random matrix model and the main theorem of

  A. Coja-Oghlan, P. Gao, M. Hahn-Klimroth, J. Lee, N. Müller, M. Rolvien,
  *The full rank condition for sparse random matrices*, arXiv:2112.14090.

## The paper's dependency graph

* Section 1.2.1, the random matrix model: degree laws `d` (variable nodes) and
  `k ≥ 3` (check nodes) with `E[d^{2+η}] + E[k^{2+η}] < ∞`, the gcds `𝔡`, `𝔨` of
  their supports, a row count `m ~ Po(d n / k)`, the conditioning on the degree
  sums agreeing (1.1), the uniform simple bipartite Tanner graph `𝔾_n(d, k)` with
  these degrees, and the matrix `𝔸 = 𝔸_n(d, k, χ)` with independent coefficients
  `χ ∈ F_q^*` on its edges; the function `Φ` of (1.2) and the full rank
  condition (1.3);
* Definition 3.1: relations, frozen coordinates, and free matrices;
* Proposition 2.1: the nullity estimate for a matrix with extra ternary rows
  (Aizenman-Sims-Starr coupling, Sections 4 and 8);
* Proposition 2.2: equitability and the truncated first moment (Section 5);
* Proposition 2.3: the bounded nonnegative basis of the frequency lattice
  (Section 6);
* Proposition 2.4: the sharp truncated second moment (Section 7);
* **Theorem 1.1**: the second-moment deduction of full row rank (Section 2.4);
* Corollary 1.2: transfer from a finite field to rational zero-one matrices.

## What is formalized here

The target of the problem is **Theorem 1.1**, stated as `P102`
and proved by `sorry`, the single `sorry` of the file.  Everything else is
proved outright:

* the deterministic linear algebra of the first version of this file (full row
  rank, solvability, right inverses, the counting of solvable right-hand sides
  over a finite field used in Section 2.1), kept unchanged;
* `NatLaw`, `DegreeParameters`, `phi` (1.2) and `StrictPhiCondition` (1.3),
  kept unchanged;
* `piLaw`, `NatLaw.toPMF`, `poissonLaw`: independent copies of a law, the
  probability mass function of a `NatLaw`, and the Poisson law;
* `DegreeProfile`, `degreeProfileLaw`, `DegreeProfile.Admissible`,
  `conditionedProfileLaw`: the degree data `(d_i)`, `m`, `(k_i)` and its
  conditioning on (1.1) and on the existence of a simple bipartite graph;
* `bipartiteGraphsWithDegrees`, `uniformBipartiteGraph`, `TannerGraph`,
  `tannerGraphLaw`: the uniform simple bipartite graph `𝔾_n(d, k)`;
* `coefficientMatrix`, `randomMatrixLaw`: the random matrix `𝔸_n(d, k, χ)`.

## Conventions

* The number of rows is random, so a sample is a `MatrixSample`: a row count
  together with a matrix with that many rows.
* Conditioning on an event of probability zero and choosing a uniform element of
  an empty set are given junk values (the unconditioned law and the empty
  graph); the paper shows the conditioning event has probability `Ω(n^{-1/2})`
  for `n` divisible by `𝔨`, and the theorem is stated along multiples of `𝔨`.
* The coefficient law `χ` is an arbitrary law on the nonzero elements of the
  field, as in the paper; the deterministic choice `χ = 1` gives the zero-one
  biadjacency matrix of Corollary 1.2.
* Full row rank is defined by solvability of every right-hand side, exactly as
  used in Section 2.1 of the paper.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

namespace SparseRandomMatrixFullRank

/-! ## Deterministic matrices and linear systems -/

/-- An `m` by `n` matrix has full row rank when every right-hand side in
`F^m` is represented by a matrix-vector product. -/
def HasFullRowRank {F m n : Type*} [Field F] [Fintype n]
    (A : Matrix m n F) : Prop :=
  Function.Surjective A.mulVec

/-- Solvability of the linear system `A x = y`. -/
def LinearSystemSolvable {F m n : Type*} [Field F] [Fintype n]
    (A : Matrix m n F) (y : m -> F) : Prop :=
  Exists fun x : n -> F => A.mulVec x = y

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

/-! ## Counting solvable right-hand sides over a finite field -/

/-- The image of `A` is precisely the vector space of solvable right-hand
sides.  Keeping it as a submodule lets Mathlib count it by its dimension. -/
def SolvableRightHandSideSpace
    {F m n : Type*} [Field F] [Fintype n] (A : Matrix m n F) :
    Submodule F (m -> F) :=
  A.mulVecLin.range

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

/- If `A` is not full row rank, multiplying the number of solvable
right-hand sides by the field order still does not exceed the total number of
right-hand sides.  Equivalently, a uniformly chosen right-hand side is
solvable with probability at most `1 / |F|`. -/
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

/-! ## Degree distributions and generating functions -/

/-- A natural-number probability distribution represented by real masses.
The second-moment summability assumption is the part of the paper's
`2 + eta` moment condition needed to define the displayed generating
function and its first derivative on `[0,1]`. -/
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

/-- The termwise first derivative of the probability generating function.
Writing the index as `r+1` avoids a truncated natural subtraction. -/
def pgfDeriv (X : NatLaw) (z : Real) : Real :=
  tsum fun r => X.mass (r + 1) * (r + 1 : Real) * z ^ r

/-- The first moment `E[X]`. -/
def mean (X : NatLaw) : Real :=
  tsum fun r => X.mass r * r

/-- `g` is the greatest common divisor of the support of `X`.
This relational form works for infinite support and states both universal
properties of a greatest common divisor. -/
def IsSupportGCD (X : NatLaw) (g : Nat) : Prop :=
  0 < g /\
    (forall r, X.mass r != 0 -> Dvd.dvd g r) /\
    forall c, 0 < c ->
      (forall r, X.mass r != 0 -> Dvd.dvd c r) -> Dvd.dvd c g

/-- The distribution is supported on natural numbers at least `lower`. -/
def SupportedAtLeast (X : NatLaw) (lower : Nat) : Prop :=
  forall r, X.mass r != 0 -> lower <= r

end NatLaw

/-! ## The paper's analytic parameter -/

/-- The row- and column-degree data in Theorem 1.1.

`variableDegree` is the paper's `d`, while `checkDegree` is its `k`.
The latter is supported on values at least three. -/
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

/-! ## Random matrix samples and asymptotic events -/

/-- A sample at size `n`.  The number of rows is random in the paper, so it is
stored as part of the sample. -/
structure MatrixSample (F : Type*) (n : Nat) where
  rowCount : Nat
  matrix : Matrix (Fin rowCount) (Fin n) F

instance matrixSampleMeasurableSpace (F : Type*) (n : Nat) :
    MeasurableSpace (MatrixSample F n) := Top.top

/-- The event that a sampled matrix has full row rank. -/
def FullRowRankEvent {F : Type*} [Field F] {n : Nat}
    (sample : MatrixSample F n) : Prop :=
  HasFullRowRank sample.matrix

/-- A sequence of events occurs with high probability when its real-valued
probability tends to one. -/
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

theorem asymptoticallyAlmostSurely_congr
    {p q : Nat -> Real} (h : forall n, p n = q n) :
    AsymptoticallyAlmostSurely p <-> AsymptoticallyAlmostSurely q := by
  cases funext h
  rfl

/-- The deterministic squeeze argument used at the end of Section 2.1.

Here `rankProbability n` is the probability of full row rank and
`solvabilityProbability n` is the probability that an independent random
right-hand side is solvable.  If a non-full-rank matrix contributes at most a
fixed proportion `c < 1` to the latter probability, asymptotic solvability
forces asymptotic full row rank. -/
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

/-- Finite-field specialization of `tendsto_one_of_solvability_gap`.  The
counting lemma above supplies the gap `1 / q` whenever the matrix is not full
row rank. -/
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

/-- The arithmetic side condition in Theorem 1.1, stated for an arbitrary
finite field rather than choosing a concrete presentation of `F_q`. -/
def FieldOrderCoprime {F : Type*} [Fintype F]
    (P : DegreeParameters) : Prop :=
  Nat.Coprime (Fintype.card F) P.variableSupportGCD


/-! ## Independent copies and the Poisson law -/

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

/-! ## The random Tanner graph (Section 1.2.1) -/

/-- The degree data of Section 1.2.1: the variable degrees `d_1, …, d_n`, the
row count `m` and the check degrees `k_1, …, k_m`. -/
structure DegreeProfile (n : Nat) where
  rowCount : Nat
  variableDegrees : Fin n -> Nat
  checkDegrees : Fin rowCount -> Nat

/-- The unconditioned law of the degree data: independent variable degrees with
law `d`, an independent row count `m ~ Po(d n / k)`, and independent check
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
/-- The degree data conditioned on admissibility.  Conditioning is meaningful
when the event has positive probability (the paper shows it is `Ω(n^{-1/2})` for
`n` divisible by `𝔨`); otherwise the unconditioned law is the junk value. -/
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

/-! ## The random matrix `𝔸_n(d, k, χ)` -/

/-- Independent coefficients with law `χ` on the edges of a Tanner graph: the
matrix `𝔸_{ij} = χ_{ij} 𝟙{a_i x_j ∈ E(𝔾)}`. -/
def coefficientMatrix {F : Type*} [Zero F] (χ : PMF F) {n : Nat} (G : TannerGraph n) :
    PMF (MatrixSample F n) :=
  (piLaw (piLaw χ n) G.rowCount).map fun c =>
    ⟨G.rowCount, Matrix.of fun i j => if G.adj i j then c i j else 0⟩

/-- The law of the random matrix `𝔸 = 𝔸_n(d, k, χ)` of Section 1.2.1. -/
def randomMatrixLaw (F : Type*) [Zero F] (P : DegreeParameters) (χ : PMF F) (n : Nat) :
    PMF (MatrixSample F n) :=
  (tannerGraphLaw P n).bind (coefficientMatrix χ)

/-! ## The main theorem -/

/-- **Theorem 1.1** (Coja-Oghlan, Gao, Hahn-Klimroth, Lee, Müller, Rolvien).
Let `d` and `k ≥ 3` be degree laws with `E[d^{2+η}] + E[k^{2+η}] < ∞` for some
`η > 0`, let `𝔡` and `𝔨` be the gcds of their supports, let `q = |F|` be coprime
to `𝔡`, and let `χ` be a law on `F ∖ {0}`.  If `Φ(z) < Φ(0)` for all `0 < z ≤ 1`,
condition (1.3), then the random matrix `𝔸 = 𝔸_n(d, k, χ)` has full row rank
over `F` with high probability as `n → ∞` along multiples of `𝔨`. -/
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

/-! ## Direct corollaries -/

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
