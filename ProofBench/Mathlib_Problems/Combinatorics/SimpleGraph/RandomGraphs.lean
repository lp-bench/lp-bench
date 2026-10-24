import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

open scoped BigOperators ENNReal
open Filter Topology

noncomputable section

namespace SpecifiedDegreeEmbedding

/-- A degree sequence on `[n]`: a list of `n` natural numbers, not required to be graphical
(see `DegreeSequence.IsGraphical`). -/
structure DegreeSequence (n : Nat) where
  degree : Fin n -> Nat

namespace DegreeSequence

/-- The total degree `∑ i, d_i` (the `ℓ¹` norm of `d`). -/
def total {n : Nat} (d : DegreeSequence n) : Nat :=
  ∑ i, d.degree i

end DegreeSequence

open DegreeSequence


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

/-- The probability of an edge set under `independentEdgeSet`. -/
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

/-- Edge weights are at most `1`. -/
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

/-- The random graph `G(n, W)`: each pair `jk` is an edge independently with probability
`W_jk`. -/
def independentEdgeGraph (n : Nat) (W : Matrix (Fin n) (Fin n) Real) :
    PMF (SimpleGraph (Fin n)) :=
  (independentEdgeSet n (edgeWeight W) (edgeWeight_le_one W)).map graphOfEdges

open scoped Classical in
/-- The simple graphs on `[n]` with degree sequence `d`. -/
def graphsWithDegrees (n : Nat) (d : DegreeSequence n) : Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G => forall i, G.degree i = d.degree i

open scoped Classical in
/-- Membership in `graphsWithDegrees`. -/
theorem mem_graphsWithDegrees {n : Nat} {d : DegreeSequence n} {G : SimpleGraph (Fin n)} :
    G ∈ graphsWithDegrees n d ↔ forall i, G.degree i = d.degree i := by
  simp [graphsWithDegrees]

/-- `d` is realisable (graphical): some simple graph on `[n]` has degree sequence `d`. -/
def DegreeSequence.IsGraphical {n : Nat} (d : DegreeSequence n) : Prop :=
  (graphsWithDegrees n d).Nonempty

open scoped Classical in
/-- `d` is graphical iff some simple graph on `[n]` has degree sequence `d`. -/
theorem DegreeSequence.isGraphical_iff {n : Nat} (d : DegreeSequence n) :
    d.IsGraphical ↔ ∃ G : SimpleGraph (Fin n), forall i, G.degree i = d.degree i := by
  simp [DegreeSequence.IsGraphical, Finset.Nonempty, mem_graphsWithDegrees]

open scoped Classical in
/-- The random graph `G(n, d)`: the uniform law on the simple graphs with degree sequence `d`
(and the junk value `⊥` when `d` is not realisable). -/
def uniformDegreeGraph (n : Nat) (d : DegreeSequence n) : PMF (SimpleGraph (Fin n)) :=
  if h : d.IsGraphical then PMF.uniformOfFinset (graphsWithDegrees n d) h else PMF.pure ⊥

/-- For graphical `d`, `G(n, d)` is the uniform law on `graphsWithDegrees n d`. -/
theorem uniformDegreeGraph_of_isGraphical {n : Nat} {d : DegreeSequence n}
    (h : d.IsGraphical) :
    uniformDegreeGraph n d = PMF.uniformOfFinset (graphsWithDegrees n d) h := by
  unfold uniformDegreeGraph
  exact dif_pos h

/-- For graphical `d`, the support of `G(n, d)` is `graphsWithDegrees n d`. -/
theorem support_uniformDegreeGraph {n : Nat} {d : DegreeSequence n} (h : d.IsGraphical) :
    (uniformDegreeGraph n d).support = graphsWithDegrees n d := by
  rw [uniformDegreeGraph_of_isGraphical h]
  exact PMF.support_uniformOfFinset h

/-- A coupling of the laws `μ` and `ν`: a joint law with marginals `μ` and `ν`. -/
structure Coupling {α β : Type*} (μ : PMF α) (ν : PMF β) where
  /-- The joint law. -/
  joint : PMF (α × β)
  /-- The first marginal is `μ`. -/
  map_fst : joint.map Prod.fst = μ
  /-- The second marginal is `ν`. -/
  map_snd : joint.map Prod.snd = ν

/-- The probability under the coupling `κ` that the first sample is `≤` the second (for graphs:
the embedding event that the first is a subgraph of the second). -/
def Coupling.embedProb {α : Type*} [LE α] {μ ν : PMF α} (κ : Coupling μ ν) : ℝ≥0∞ :=
  κ.joint.toOuterMeasure {p | p.1 <= p.2}

/-- A probability mass function gives every set measure at most `1`. -/
theorem toOuterMeasure_le_one {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s <= 1 :=
  calc p.toOuterMeasure s <= p.toOuterMeasure Set.univ :=
        p.toOuterMeasure_mono fun x _ => Set.mem_univ x
    _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)

/-- The embedding probability is at most `1`. -/
theorem Coupling.embedProb_le_one {α : Type*} [LE α] {μ ν : PMF α} (κ : Coupling μ ν) :
    κ.embedProb <= 1 :=
  toOuterMeasure_le_one _ _

end SpecifiedDegreeEmbedding

end
