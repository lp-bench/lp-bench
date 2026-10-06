import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/- ---------------------------------------------------- -/
/- Paper: Embedding theorems for random graphs with specified degrees -/
/- ---------------------------------------------------- -/

/-!
# P050: Embedding theorems for random graphs with specified degrees

This file formalizes the random graph models of Section 1 and the main theorem
of

  P. Gao and Y. Ohapkin, *Embedding theorems for random graphs with specified
  degrees*, arXiv:2302.09729.

## The paper's dependency graph

* Section 1: for a symmetric matrix `W ∈ [0,1]^{[n] × [n]}`, `G(n, W)` is the
  random graph in which each pair `jk` is an edge independently with
  probability `W_jk`; for a realisable degree sequence `d`, `G(n, d)` is the
  uniformly random simple graph with degree sequence `d`.  `Δ(d)` and `δ(d)`
  are the maximum and minimum degree, `‖d‖₁ = Σ d_i`, and
  `J(d) = Σ_{i=1}^{d_1} d_i` is the sum of the `Δ(d)` largest degrees.
  Proposition 1.3 (a corollary of [20, Theorem 1]): if `J(d) = o(‖d‖₁)` then
  `P(jk ∈ G(n, d)) = (1 + O(J(d)/‖d‖₁)) d_j d_k / (‖d‖₁ + d_j d_k)`, which
  motivates Definition 1.6, the matrix `P(d)` with entries
  `d_i d_j / (‖d‖₁ + d_i d_j)`.
* **Theorem 1.8**, the main theorem: if `J(d) = o(‖d‖₁)` and `δ(d) ≫ log n`,
  there are `ε = o(1)` and a coupling `(G_L, G)` with `G_L ~ G(n, W)`,
  `W = (1 - ε) f(P(d))`, `f(x) = 1 - e^{-x}`, and `G ~ G(n, d)`, such that
  `P(G_L ⊆ G) = 1 - o(1)`.
* Theorem 1.7: the same for `W = (1 - ε) P(d)` under the stronger hypothesis
  `Δ(d)² = o(‖d‖₁)`; the paper derives it from Theorem 1.8 since
  `J(d) ≤ Δ(d)²`, `Δ(d)² = o(‖d‖₁)` forces `P(d)_jk = o(1)` uniformly, and
  `1 - e^{-x} = (1 + O(x)) x`, so that `f(P(d)) = (1 + o(1)) P(d)`.
* Theorem 1.11: applications (Hamiltonicity, `k`-connectivity, minors,
  spanning subgraphs of bounded degree) obtained by embedding `G(n, p)` into
  `G(n, W)` (the nesting property of Section 1.2) and `G(n, W)` into `G(n, d)`.
* Section 2, the coupling: the sequential procedure `SeqApprox-P(d, λ, Λ)`
  (Definition 2.1, Lemma 2.2: its output is `G(n, f(λ Λ ⊙ Q(d)))`), the
  sequential procedure `SeqSample-D(d)` (Lemma 2.3, Corollary 2.4: its output
  is `G(n, d)`; Lemma 2.5, Chernoff-type tail bounds; Lemma 2.6, concentration
  of the remaining degrees),
  the procedure `Coupling(d, λ, Λ)` (Lemma 2.7: the marginals are
  `G(n, f(λ Λ ⊙ Q))` and `G(n, d)`, and `G_L ⊆ G` unless the fallback
  `IndSample` is called), and the choice of the parameters (2)-(7).
* Section 3, the proof of Theorem 1.8: (8) `IndSample` is called with
  probability `o(1)` (Lemma 2.5, Lemma 2.6, Theorem 3.1 on conditional edge
  probabilities), and (9) `λ Λ ⊙ Q = (1 + o(1)) P`.
* Appendix: Proposition 3.2 (`Δ(d) = o(n)` and few pairs with
  `d_i d_j ≥ ε ‖d‖₁` under `J(d) = o(‖d‖₁)`) and Example 3.3.

## What is formalized here

The target of the problem is **Theorem 1.8**, stated at the end of this file as
`P107` and proved by `sorry`, the single `sorry` of the file.
Everything else is proved from first principles with no `sorry` and no new
axiom:

* `DegreeSequence`, `total`, `edgeParameter`, `edgeMatrix`, `poissonize`: the
  degree sequences, `‖d‖₁`, the matrix `P(d)` of Definition 1.6 and the map
  `f(x) = 1 - e^{-x}`, with their elementary range and symmetry facts;
* `maxDegree`, `minDegree`, `topDegreeSum`: `Δ(d)`, `δ(d)` and `J(d)`, the
  latter as the largest sum of `Δ(d)` distinct degrees;
* `independentEdgeSet`, `independentEdgeGraph`: the law `G(n, W)`, built as the
  product law on edge sets (`P(E) = Π_{e ∈ E} W_e Π_{e ∉ E} (1 - W_e)`, proved
  to sum to `1`) pushed to simple graphs;
* `graphsWithDegrees`, `IsGraphical`, `uniformDegreeGraph`: the realisable
  degree sequences and the uniform law `G(n, d)`;
* `Coupling`, `Coupling.embedProb`: couplings of two laws (a joint law with the
  prescribed marginals) and the probability `P(G_L ⊆ G)` of the embedding
  event.

## What is deliberately not asserted

* Theorem 1.7 is not stated: the paper derives it from Theorem 1.8, and the
  file carries a single `sorry`.  Its hypothesis `Δ(d)² = o(‖d‖₁)` implies the
  hypothesis `J(d) = o(‖d‖₁)` of the target (`topDegreeSum_le_sq`).
* The sequential procedures of Section 2 and Theorem 1.11 are not encoded.
* Nothing about the rate of the `o(1)` terms is asserted.

## Conventions

* `n` ranges over all of `ℕ`, the vertex set is `Fin n`, and the paper's
  sequence of degree sequences `d = d(n)` is a dependent function
  `d : ∀ n, DegreeSequence n`.  Asymptotic conditions are `Filter.Tendsto`
  statements: `J(d) = o(‖d‖₁)` is `J(d(n)) / ‖d(n)‖₁ → 0`, and
  `δ(d) ≫ log n` is `δ(d(n)) / log n → ∞`.
* Random graphs are `PMF`s on Mathlib's `SimpleGraph (Fin n)`, which is a
  finite type; probabilities live in `ℝ≥0∞`.
* The entries of `W` are read on unordered pairs through the sorted pair
  `(min j k, max j k)` and clamped to `[0, 1]`; for a symmetric matrix with
  entries in `[0, 1]`, the only case that occurs, this is exactly `W_jk`
  (`edgeWeight_mk`).
* `G(n, d)` is defined for every `d`, with the junk value `⊥` when `d` is not
  realisable; the main theorem assumes realisability for every `n`, where the
  paper assumes it for all large `n` (nothing in the conclusion depends on
  finitely many `n`).
* Real division by `0` and `Real.log 0 = Real.log 1 = 0` make the two
  asymptotic quotients `0` for `n ≤ 1` (and when `‖d(n)‖₁ = 0`); this is
  harmless since `δ(d) ≫ log n` forces `δ(d(n)) ≥ 1`, hence `‖d(n)‖₁ > 0`, for
  all large `n`, and the paper's `o` and `≫` (Section 1) also only concern
  large `n`.
* The parameter `ε` of the main theorem is required to lie in `[0, 1]`, so that
  `(1 - ε) f(P(d))` is a matrix of probabilities.  The paper only asserts
  `ε = o(1)`: `ε ≥ 0` is without loss of generality by the nesting property of
  `G(n, W)` (Section 1.2), and `ε ≤ 1` can fail for at most finitely many `n`,
  where `ε = 1` (`W = 0`) embeds trivially.  In the paper's proof `ε` is the
  uniform slack in (9), `λ Λ ⊙ Q = (1 + o(1)) P`.
-/

open scoped BigOperators ENNReal
open Filter Topology

noncomputable section

namespace SpecifiedDegreeEmbedding

/-- A degree sequence on `[n]`.  Graphicality is deliberately kept as a
separate hypothesis because several deterministic estimates only use the
numbers themselves. -/
structure DegreeSequence (n : Nat) where
  degree : Fin n -> Nat

namespace DegreeSequence

/-- The `l1` norm appearing throughout the paper. -/
def total {n : Nat} (d : DegreeSequence n) : Nat :=
  ∑ i, d.degree i

/-- Definition 1.6 off the diagonal:
`d_i d_j / (||d||_1 + d_i d_j)`. -/
def edgeParameter {n : Nat} (d : DegreeSequence n) (i j : Fin n) : Real :=
  if i = j then 0
  else
    ((d.degree i : Real) * (d.degree j : Real)) /
      ((d.total : Real) +
        (d.degree i : Real) * (d.degree j : Real))

/-- The symmetric matrix `P(d)` from Definition 1.6. -/
def edgeMatrix {n : Nat} (d : DegreeSequence n) : Matrix (Fin n) (Fin n) Real :=
  fun i j => d.edgeParameter i j

@[simp]
theorem edgeParameter_self {n : Nat} (d : DegreeSequence n) (i : Fin n) :
    d.edgeParameter i i = 0 := by
  simp [edgeParameter]

theorem edgeParameter_symm {n : Nat} (d : DegreeSequence n) (i j : Fin n) :
    d.edgeParameter i j = d.edgeParameter j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : Not (j = i) := fun h => hij h.symm
    simp [edgeParameter, hij, hji, mul_comm]

theorem edgeMatrix_transpose {n : Nat} (d : DegreeSequence n) :
    d.edgeMatrix.transpose = d.edgeMatrix := by
  ext i j
  exact d.edgeParameter_symm j i

@[simp]
theorem edgeMatrix_apply_self {n : Nat} (d : DegreeSequence n) (i : Fin n) :
    d.edgeMatrix i i = 0 :=
  d.edgeParameter_self i

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

theorem edgeParameter_le_one {n : Nat} (d : DegreeSequence n)
    (htotal : 0 < d.total) (i j : Fin n) :
    d.edgeParameter i j <= 1 := by
  by_cases hij : i = j
  · simp [edgeParameter, hij]
  · exact (d.edgeParameter_lt_one htotal hij).le

/-- Applying `1 - exp(-x)` entrywise is the Poissonization used in Theorem
1.8. -/
def poissonize (x : Real) : Real :=
  1 - Real.exp (-x)

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

/-! ### The maximum degree `Δ(d)`, the minimum degree `δ(d)` and `J(d)` -/

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

/-! ## Random graphs with independent edges: `G(n, W)` -/

/-- The potential edges of a simple graph on `[n]`: the unordered pairs `jk` with `j ≠ k`. -/
abbrev Edge (n : Nat) := {e : Sym2 (Fin n) // Not e.IsDiag}

/-- The law of the edge set of `G(n, W)`, for edge probabilities `w e <= 1`: the edge set `t`
has probability `Π_{e ∈ t} w e · Π_{e ∉ t} (1 - w e)`, i.e. every potential edge is present
independently with probability `w e`. -/
def independentEdgeSet (n : Nat) (w : Edge n -> ℝ≥0∞) (hw : forall e, w e <= 1) :
    PMF (Finset (Edge n)) :=
  ⟨fun t => (∏ e ∈ t, w e) * ∏ e ∈ tᶜ, (1 - w e), by
    have hsum : ∑ t : Finset (Edge n), (∏ e ∈ t, w e) * ∏ e ∈ tᶜ, (1 - w e) = 1 := by
      calc ∑ t : Finset (Edge n), (∏ e ∈ t, w e) * ∏ e ∈ tᶜ, (1 - w e)
          = ∑ t ∈ (Finset.univ : Finset (Edge n)).powerset,
              (∏ e ∈ t, w e) * ∏ e ∈ Finset.univ \ t, (1 - w e) := by
            rw [Finset.powerset_univ]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [Finset.compl_eq_univ_sdiff]
        _ = ∏ e ∈ (Finset.univ : Finset (Edge n)), (w e + (1 - w e)) :=
            (Finset.prod_add _ _ _).symm
        _ = 1 := Finset.prod_eq_one fun e _ => add_tsub_cancel_of_le (hw e)
    have hfin := hasSum_fintype fun t : Finset (Edge n) => (∏ e ∈ t, w e) * ∏ e ∈ tᶜ, (1 - w e)
    rw [hsum] at hfin
    exact hfin⟩

theorem independentEdgeSet_apply (n : Nat) (w : Edge n -> ℝ≥0∞) (hw : forall e, w e <= 1)
    (t : Finset (Edge n)) :
    independentEdgeSet n w hw t = (∏ e ∈ t, w e) * ∏ e ∈ tᶜ, (1 - w e) :=
  rfl

/-- The simple graph on `[n]` whose edge set is `t`. -/
def graphOfEdges {n : Nat} (t : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (t : Set (Edge n)))

/-- The probability of the potential edge `jk` prescribed by the matrix `W`: the entry
`W (min j k) (max j k)`, clamped to `[0, 1]`.  For a symmetric matrix with entries in
`[0, 1]` this is `W_jk` (`edgeWeight_mk`). -/
def edgeWeight {n : Nat} (W : Matrix (Fin n) (Fin n) Real) (e : Edge n) : ℝ≥0∞ :=
  min (ENNReal.ofReal (Sym2.lift ⟨fun j k => W (min j k) (max j k), fun j k => by
    change W (min j k) (max j k) = W (min k j) (max k j)
    rw [min_comm, max_comm]⟩ e.1)) 1

theorem edgeWeight_le_one {n : Nat} (W : Matrix (Fin n) (Fin n) Real) (e : Edge n) :
    edgeWeight W e <= 1 :=
  min_le_right _ _

/-- On a symmetric matrix with entries at most `1`, `edgeWeight` reads off `W_jk`. -/
theorem edgeWeight_mk {n : Nat} {W : Matrix (Fin n) (Fin n) Real}
    (hsymm : forall j k, W j k = W k j) (hW : forall j k, W j k <= 1) {j k : Fin n}
    (h : Not (s(j, k) : Sym2 (Fin n)).IsDiag) :
    edgeWeight W ⟨s(j, k), h⟩ = ENNReal.ofReal (W j k) := by
  have hmm : W (min j k) (max j k) = W j k := by
    rcases le_total j k with hjk | hjk
    · rw [min_eq_left hjk, max_eq_right hjk]
    · rw [min_eq_right hjk, max_eq_left hjk, hsymm]
  dsimp only [edgeWeight]
  rw [Sym2.lift_mk]
  change min (ENNReal.ofReal (W (min j k) (max j k))) 1 = ENNReal.ofReal (W j k)
  rw [hmm, min_eq_left (ENNReal.ofReal_le_one.mpr (hW j k))]

/-- The random graph `G(n, W)` of Section 1: each pair `jk` is an edge independently with
probability `W_jk`. -/
def independentEdgeGraph (n : Nat) (W : Matrix (Fin n) (Fin n) Real) :
    PMF (SimpleGraph (Fin n)) :=
  (independentEdgeSet n (edgeWeight W) (edgeWeight_le_one W)).map graphOfEdges

/-! ## Uniformly random graphs with a given degree sequence: `G(n, d)` -/

open scoped Classical in
/-- The simple graphs on `[n]` with degree sequence `d`. -/
def graphsWithDegrees (n : Nat) (d : DegreeSequence n) : Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G => forall i, G.degree i = d.degree i

open scoped Classical in
theorem mem_graphsWithDegrees {n : Nat} {d : DegreeSequence n} {G : SimpleGraph (Fin n)} :
    G ∈ graphsWithDegrees n d ↔ forall i, G.degree i = d.degree i := by
  simp [graphsWithDegrees]

/-- `d` is realisable (graphical): some simple graph on `[n]` has degree sequence `d`. -/
def DegreeSequence.IsGraphical {n : Nat} (d : DegreeSequence n) : Prop :=
  (graphsWithDegrees n d).Nonempty

open scoped Classical in
theorem DegreeSequence.isGraphical_iff {n : Nat} (d : DegreeSequence n) :
    d.IsGraphical ↔ ∃ G : SimpleGraph (Fin n), forall i, G.degree i = d.degree i := by
  simp [DegreeSequence.IsGraphical, Finset.Nonempty, mem_graphsWithDegrees]

open scoped Classical in
/-- The random graph `G(n, d)`: the uniform law on the simple graphs with degree sequence `d`
(and the junk value `⊥` when `d` is not realisable). -/
def uniformDegreeGraph (n : Nat) (d : DegreeSequence n) : PMF (SimpleGraph (Fin n)) :=
  if h : d.IsGraphical then PMF.uniformOfFinset (graphsWithDegrees n d) h else PMF.pure ⊥

theorem uniformDegreeGraph_of_isGraphical {n : Nat} {d : DegreeSequence n}
    (h : d.IsGraphical) :
    uniformDegreeGraph n d = PMF.uniformOfFinset (graphsWithDegrees n d) h := by
  unfold uniformDegreeGraph
  exact dif_pos h

theorem support_uniformDegreeGraph {n : Nat} {d : DegreeSequence n} (h : d.IsGraphical) :
    (uniformDegreeGraph n d).support = graphsWithDegrees n d := by
  rw [uniformDegreeGraph_of_isGraphical h]
  exact PMF.support_uniformOfFinset h

/-! ## Couplings -/

/-- A coupling of the laws `μ` and `ν`: a joint law with marginals `μ` and `ν`. -/
structure Coupling {α β : Type*} (μ : PMF α) (ν : PMF β) where
  /-- The joint law. -/
  joint : PMF (α × β)
  /-- The first marginal is `μ`. -/
  map_fst : joint.map Prod.fst = μ
  /-- The second marginal is `ν`. -/
  map_snd : joint.map Prod.snd = ν

/-- The probability of the embedding event `G_L ⊆ G` under a coupling. -/
def Coupling.embedProb {α : Type*} [LE α] {μ ν : PMF α} (κ : Coupling μ ν) : ℝ≥0∞ :=
  κ.joint.toOuterMeasure {p | p.1 <= p.2}

theorem toOuterMeasure_le_one {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s <= 1 :=
  calc p.toOuterMeasure s <= p.toOuterMeasure Set.univ :=
        p.toOuterMeasure_mono fun x _ => Set.mem_univ x
    _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)

theorem Coupling.embedProb_le_one {α : Type*} [LE α] {μ ν : PMF α} (κ : Coupling μ ν) :
    κ.embedProb <= 1 :=
  toOuterMeasure_le_one _ _

/-! ## The main theorem -/

/-- **Theorem 1.8** (Gao, Ohapkin).  Let `d = d(n)` be realisable degree sequences with
`J(d) = o(‖d‖₁)` and `δ(d) ≫ log n`.  Then there are `ε = ε(n) = o(1)` and couplings
`(G_L, G)` with `G_L ~ G(n, W)`, `W = (1 - ε) f(P(d))` where `f(x) = 1 - e^{-x}` and `P(d)` is
the matrix of Definition 1.6, and `G ~ G(n, d)`, such that `P(G_L ⊆ G) = 1 - o(1)`. -/
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

/-! ## Direct corollaries -/

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
