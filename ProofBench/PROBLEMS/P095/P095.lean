import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# P095: Explicit two-sided unique-neighbor expanders

This file formalizes part of

  J.-T. Hsieh, T. McKenzie, S. Mohanty and P. Paredes,
  *Explicit two-sided unique-neighbor expanders*, arXiv:2302.01212.

The paper's dependency graph for its main theorems is:

* Definition 1.1: two-sided (algebraic) unique-neighbour expanders;
* Lemma 2.1: the expander mixing lemma bound `e(S) <= D|S|(eps + delta)/2`;
* **Lemma 2.2**: in a graph of hereditarily bounded average degree, a constant
  fraction of the edges is incident to low-degree vertices;
* Fact 2.3 (Ihara-Bass) and Lemma 2.4: the spectral radius of the
  non-backtracking matrix versus positive definiteness of the Bethe Hessian;
* Definition 3.1: the *line product* `G (x) H`, and Definition 3.2, the
  unique-neighbour expansion profile `P_H`;
* Lemma 3.3: the expansion profile of the line product, whose proof combines
  Definition 3.1, Definition 3.2 and Lemma 2.2;
* Theorem 1.2 (Section 4), Theorem 1.8 (Section 5), Theorem 1.11 (Section 6),
  Theorem 1.12 (Appendix A) and Theorem 1.5 (Section 7).

The target of the problem is the paper's main theorem -- **Theorem 4.4**, the
formal version of Theorem 1.2 -- stated at the end of this file as
`twoSided_uniqueNeighbour_expanders_exist` and proved by `sorry`, the single
`sorry` of the file: for every `beta` in `(0, 1/2]` there are `d0, delta > 0`
such that for all even `d1, d2 >= d0` with `1 >= d1/d2 >= beta/(1-beta)`
there is an infinite family of `(2 d1, 2 d2)`-biregular bipartite graphs in
which every vertex set `S` with `|S| <= |V|/d1^3` has at least
`delta * d1 * |S|` unique neighbours.

Everything else below is proved from first principles with no `sorry` and no
new axioms.  The results formalized in full are

* `pairs`, the ordered-pair edge count, together with its double-counting,
  symmetry and additivity lemmas;
* `two_mul_edges_le_three_mul_sum_lowDegree`, which is **Lemma 2.2**;
* `lineProductNbr` (Definition 3.1) and `nbhd_lineProduct`, the decomposition of
  neighbourhoods in the line product into the gadget copies `H(v)`, which is the
  first step in the proof of Lemma 3.3;
* `HasExpansionProfileAtLeast` (Definition 3.2) and
  `TwoSidedUniqueNeighbourExpander` (Definition 1.1).

The spectral half of the paper (Lemma 2.1, Fact 2.3, Lemma 2.4, Theorems 1.8,
1.11 and 1.12) is not asserted here, and neither is Lemma 3.3, whose proof needs
those inputs in addition to Lemma 2.2.
-/

namespace TwoSidedUniqueNeighbour

open Finset

/-! ## Ordered-pair edge counts

`pairs F s t` is the number of ordered pairs `(u, v)` of `s x t` joined by an
edge.  For `s = t` this is `2 e(s)`, and for disjoint `s` and `t` it is the
paper's `e(s, t)`. -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : SimpleGraph V) [DecidableRel F.Adj]

/-- The number of ordered adjacent pairs in `s x t`. -/
def pairs (s t : Finset V) : ℕ :=
  ((s ×ˢ t).filter fun p => F.Adj p.1 p.2).card

omit [Fintype V] [DecidableEq V] in
/-- Double counting: `pairs F s t` is the sum over `s` of the number of
neighbours inside `t`. -/
theorem pairs_eq_sum (s t : Finset V) :
    pairs F s t = ∑ u ∈ s, (t.filter fun v => F.Adj u v).card := by
  rw [pairs, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

omit [Fintype V] [DecidableEq V] in
/-- `pairs` is symmetric, since adjacency is. -/
theorem pairs_comm (s t : Finset V) : pairs F s t = pairs F t s := by
  classical
  have himg : ((t ×ˢ s).filter fun p => F.Adj p.1 p.2)
      = (((s ×ˢ t).filter fun p => F.Adj p.1 p.2)).image Prod.swap := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hadj⟩
      exact ⟨(p.2, p.1), ⟨⟨hp2, hp1⟩, hadj.symm⟩, rfl⟩
    · rintro ⟨q, ⟨⟨hq1, hq2⟩, hadj⟩, rfl⟩
      exact ⟨⟨hq2, hq1⟩, hadj.symm⟩
  rw [pairs, pairs, himg, Finset.card_image_of_injective _ Prod.swap_injective]

omit [Fintype V] in
/-- `pairs` is additive in its first argument along a disjoint union. -/
theorem pairs_union_left {s₁ s₂ : Finset V} (h : Disjoint s₁ s₂) (t : Finset V) :
    pairs F (s₁ ∪ s₂) t = pairs F s₁ t + pairs F s₂ t := by
  rw [pairs_eq_sum, pairs_eq_sum, pairs_eq_sum, Finset.sum_union h]

omit [Fintype V] in
/-- `pairs` is additive in its second argument along a disjoint union. -/
theorem pairs_union_right (s : Finset V) {t₁ t₂ : Finset V} (h : Disjoint t₁ t₂) :
    pairs F s (t₁ ∪ t₂) = pairs F s t₁ + pairs F s t₂ := by
  rw [pairs_comm, pairs_comm F s t₁, pairs_comm F s t₂, pairs_union_left F h]

omit [DecidableEq V] in
/-- Summing degrees over `s` counts the ordered pairs leaving `s`. -/
theorem pairs_univ_eq_sum_degree (s : Finset V) :
    pairs F s Finset.univ = ∑ u ∈ s, F.degree u := by
  rw [pairs_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext v
  simp [SimpleGraph.mem_neighborFinset]

/-! ## Lemma 2.2: most edges touch a low-degree vertex -/

/-- The vertices of degree at most `2 * gamma`. -/
noncomputable def lowDegree (gamma : ℝ) : Finset V :=
  Finset.univ.filter fun v => (F.degree v : ℝ) ≤ 2 * gamma

/-- The vertices of degree more than `2 * gamma`. -/
noncomputable def highDegree (gamma : ℝ) : Finset V :=
  Finset.univ.filter fun v => ¬ ((F.degree v : ℝ) ≤ 2 * gamma)

omit [DecidableEq V] in
theorem disjoint_lowDegree_highDegree (gamma : ℝ) :
    Disjoint (lowDegree F gamma) (highDegree F gamma) :=
  Finset.disjoint_filter_filter_not _ _ _

theorem lowDegree_union_highDegree (gamma : ℝ) :
    lowDegree F gamma ∪ highDegree F gamma = Finset.univ :=
  Finset.filter_union_filter_not_eq _ _

omit [DecidableEq V] in
theorem two_mul_gamma_lt_degree_of_mem_highDegree {gamma : ℝ} {v : V}
    (hv : v ∈ highDegree F gamma) : 2 * gamma < (F.degree v : ℝ) :=
  not_le.mp (Finset.mem_filter.mp hv).2

omit [DecidableEq V] in
/-- **Lemma 2.2.**  Let `F` be a graph in which every induced subgraph has
average degree at most `gamma`, that is `2 e(S) <= gamma |S|` for every set `S`
of vertices.  Split the vertices into those of degree at most `2 gamma` and the
rest.  Then at least a third of the ordered edge pairs is accounted for by the
degrees of the low-degree vertices:
`2 e(F) <= 3 * (sum of deg(v) over the low-degree vertices)`. -/
theorem two_mul_edges_le_three_mul_sum_lowDegree (gamma : ℝ)
    (hgamma : ∀ s : Finset V, (pairs F s s : ℝ) ≤ gamma * s.card) :
    pairs F Finset.univ Finset.univ
      ≤ 3 * ∑ v ∈ lowDegree F gamma, F.degree v := by
  classical
  have hdisj : Disjoint (lowDegree F gamma) (highDegree F gamma) :=
    disjoint_lowDegree_highDegree F gamma
  have hunion : lowDegree F gamma ∪ highDegree F gamma = Finset.univ :=
    lowDegree_union_highDegree F gamma
  -- the degrees of the high-degree vertices split into internal and crossing pairs
  have hdegh : ∑ v ∈ highDegree F gamma, F.degree v
      = pairs F (highDegree F gamma) (highDegree F gamma)
        + pairs F (highDegree F gamma) (lowDegree F gamma) := by
    have h := pairs_union_right F (highDegree F gamma) hdisj
    rw [hunion] at h
    rw [← pairs_univ_eq_sum_degree, h]
    omega
  -- and likewise for the low-degree vertices
  have hdegl : ∑ v ∈ lowDegree F gamma, F.degree v
      = pairs F (lowDegree F gamma) (lowDegree F gamma)
        + pairs F (highDegree F gamma) (lowDegree F gamma) := by
    have h := pairs_union_right F (lowDegree F gamma) hdisj
    rw [hunion] at h
    have hsym : pairs F (lowDegree F gamma) (highDegree F gamma)
        = pairs F (highDegree F gamma) (lowDegree F gamma) := pairs_comm F _ _
    rw [← pairs_univ_eq_sum_degree, h, hsym]
  -- all ordered edge pairs
  have htotal : pairs F Finset.univ Finset.univ
      = ∑ v ∈ lowDegree F gamma, F.degree v + ∑ v ∈ highDegree F gamma, F.degree v := by
    have h := pairs_union_left F hdisj Finset.univ
    rw [hunion] at h
    rw [h, pairs_univ_eq_sum_degree, pairs_univ_eq_sum_degree]
  -- the key inequality `2 e(F_h) <= e(F_h, F_l)`, from the hereditary bound
  have hPC : pairs F (highDegree F gamma) (highDegree F gamma)
      ≤ pairs F (highDegree F gamma) (lowDegree F gamma) := by
    have h1 : (pairs F (highDegree F gamma) (highDegree F gamma) : ℝ)
        ≤ gamma * ((highDegree F gamma).card : ℝ) := hgamma _
    have h2 : ((highDegree F gamma).card : ℝ) * (2 * gamma)
        ≤ ∑ v ∈ highDegree F gamma, (F.degree v : ℝ) := by
      have hle : ∀ v ∈ highDegree F gamma, (2 * gamma : ℝ) ≤ (F.degree v : ℝ) :=
        fun v hv => (two_mul_gamma_lt_degree_of_mem_highDegree F hv).le
      have h := Finset.sum_le_sum hle
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    have h3 : ∑ v ∈ highDegree F gamma, (F.degree v : ℝ)
        = (pairs F (highDegree F gamma) (highDegree F gamma) : ℝ)
          + (pairs F (highDegree F gamma) (lowDegree F gamma) : ℝ) := by
      have := hdegh
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
    rw [h3] at h2
    have h4 : (pairs F (highDegree F gamma) (highDegree F gamma) : ℝ)
        ≤ (pairs F (highDegree F gamma) (lowDegree F gamma) : ℝ) := by nlinarith [h1, h2]
    exact_mod_cast h4
  omega

/-! ## The line product (Definition 3.1)

`G` is a `D`-regular base graph; for a vertex `v` of `G` and an index `i` in
`[D]`, `inc v i` is the `i`-th edge incident to `v`.  The gadget `H` is a graph
on `[D]`.  The line product `G (x) H` has vertex set `E(G)` and, for every
vertex `v` of `G`, a copy `H(v)` of `H` placed on the edges incident to `v`. -/

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq E]

/-- The neighbourhood function of the line product `G (x) H` of
Definition 3.1. -/
def lineProductNbr {D : ℕ} (inc : W → Fin D → E) (H : SimpleGraph (Fin D))
    [DecidableRel H.Adj] (a : E) : Finset E :=
  Finset.univ.filter fun b : E =>
    ∃ v : W, ∃ i : Fin D, ∃ j : Fin D, H.Adj i j ∧ inc v i = a ∧ inc v j = b

/-- `N(S)` for a graph presented by a neighbourhood function. -/
def nbhd {α β : Type*} [DecidableEq β] (nbr : α → Finset β) (S : Finset α) : Finset β :=
  S.biUnion nbr

/-- The trace of a set `T` of `G`-edges on the gadget copy `H(v)`. -/
def copyTrace {D : ℕ} (inc : W → Fin D → E) (T : Finset E) (v : W) : Finset (Fin D) :=
  Finset.univ.filter fun i => inc v i ∈ T

/-- The `H`-neighbourhood of a set of gadget indices. -/
def gadgetNbhd {D : ℕ} (H : SimpleGraph (Fin D)) [DecidableRel H.Adj]
    (A : Finset (Fin D)) : Finset (Fin D) :=
  A.biUnion fun i => Finset.univ.filter fun j => H.Adj i j

/-- **Definition 3.1, unfolded.**  In the line product, the neighbourhood of a
set `T` of vertices (that is, of `G`-edges) is the union over the base vertices
`v` of the images under `inc v` of the `H`-neighbourhoods of the traces `T(v)`.
This decomposition into the copies `H(v)` is the starting point of the proof of
Lemma 3.3. -/
theorem nbhd_lineProduct {D : ℕ} (inc : W → Fin D → E) (H : SimpleGraph (Fin D))
    [DecidableRel H.Adj] (T : Finset E) :
    nbhd (lineProductNbr inc H) T
      = Finset.univ.biUnion fun v : W =>
          (gadgetNbhd H (copyTrace inc T v)).image (inc v) := by
  classical
  ext b
  simp only [nbhd, Finset.mem_biUnion, lineProductNbr, Finset.mem_filter,
    Finset.mem_univ, true_and, gadgetNbhd, copyTrace, Finset.mem_image]
  constructor
  · rintro ⟨a, haT, v, i, j, hij, hinc, hincb⟩
    exact ⟨v, j, ⟨i, hinc ▸ haT, hij⟩, hincb⟩
  · rintro ⟨v, j, ⟨i, hiT, hij⟩, hincb⟩
    exact ⟨inc v i, hiT, v, i, j, hij, rfl, hincb⟩

/-! ## Unique-neighbour expansion (Definitions 1.1 and 3.2) -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `UN(S)`, the unique neighbours of `S` for a graph presented by a
neighbourhood function. -/
def uniqueNeighbours {β : Type*} [Fintype β] [DecidableEq β] (nbr : α → Finset β)
    (S : Finset α) : Finset β :=
  Finset.univ.filter fun v => (S.filter fun u => v ∈ nbr u).card = 1

/-- **Definition 3.2.**  The statement `P_H(t) >= c` for the unique-neighbour
expansion profile: every nonempty set of at most `t` vertices has at least
`c |S|` unique neighbours. -/
def HasExpansionProfileAtLeast {β : Type*} [Fintype β] [DecidableEq β]
    (nbr : α → Finset β) (t : ℕ) (c : ℝ) : Prop :=
  ∀ S : Finset α, S.Nonempty → S.card ≤ t →
    c * (S.card : ℝ) ≤ ((uniqueNeighbours nbr S).card : ℝ)

omit [Fintype α] [DecidableEq α] in
/-- The profile is antitone in the size threshold: a bound valid up to `t`
remains valid up to any smaller threshold. -/
theorem HasExpansionProfileAtLeast.mono {β : Type*} [Fintype β] [DecidableEq β]
    {nbr : α → Finset β} {t t' : ℕ} {c : ℝ}
    (h : HasExpansionProfileAtLeast nbr t c) (htt : t' ≤ t) :
    HasExpansionProfileAtLeast nbr t' c :=
  fun S hne hcard => h S hne (hcard.trans htt)

/-- **Definition 1.1.**  A `(d1, d2)`-biregular graph, presented by the two
neighbourhood functions of its sides, is a `delta`-two-sided unique-neighbour
expander with expansion factor `alpha` when both sides expand: every left set of
density below `delta` has at least `alpha d1 |S|` neighbours, and symmetrically
on the right. -/
def TwoSidedUniqueNeighbourExpander {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] (nbrL : L → Finset R) (nbrR : R → Finset L)
    (d1 d2 : ℕ) (alpha delta : ℝ) : Prop :=
  (∀ S : Finset L, (S.card : ℝ) < delta * (Fintype.card L : ℝ) →
      alpha * (d1 * S.card) ≤ ((nbhd nbrL S).card : ℝ)) ∧
    (∀ S : Finset R, (S.card : ℝ) < delta * (Fintype.card R : ℝ) →
      alpha * (d2 * S.card) ≤ ((nbhd nbrR S).card : ℝ))

/-! ## Theorem 4.4: the main theorem -/

end TwoSidedUniqueNeighbour

open TwoSidedUniqueNeighbour in
open scoped Classical in
/-- **Theorem 4.4, the formal version of Theorem 1.2** -- the main theorem of
the paper.  For every `beta` in `(0, 1/2]` there are `d0 = d0(beta) > 0` and
`delta = delta(beta) > 0` such that for all even `d1, d2 >= d0` with
`1 >= d1/d2 >= beta/(1-beta)`, there is an infinite family of
`(2 d1, 2 d2)`-biregular bipartite graphs -- graphs on arbitrarily many
vertices below -- in which every vertex set `S` with
`|S| <= |V(Z)| / d1 ^ 3` has at least `delta * d1 * |S|` unique neighbours;
in the language of Definition 3.2, `P_Z(|V(Z)| / d1 ^ 3) >= delta * d1`.

Encoding notes.  The aspect-ratio window `1 >= d1/d2 >= beta/(1-beta)` is
written multiplicatively as `d1 <= d2` and `beta * d2 <= (1 - beta) * d1`
(sound since `1 - beta >= 1/2 > 0`).  The threshold `N / d1 ^ 3` uses
natural-number division, which agrees with the paper's
`|S| <= |V(Z_n)| / d1^3` because `|S|` is an integer.  The bipartition is
recorded by `side`, with the `2 d1`-regular side on `true`; every edge
crosses sides.  The paper's *strong explicitness* of the family and the
Cayley group action of Theorem 1.2 (the "algebraic" refinement) are
properties of the construction that the paper's own formal statement,
Theorem 4.4, does not assert, and they are likewise not asserted here.

This is the target statement of problem P095; its `sorry` is the only one in
the file. -/
theorem P095 {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1 / 2) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ d₁ d₂ : ℕ, d₀ ≤ d₁ → d₀ ≤ d₂ → Even d₁ → Even d₂ → d₁ ≤ d₂ →
        β * (d₂ : ℝ) ≤ (1 - β) * (d₁ : ℝ) →
        ∀ n₀ : ℕ, ∃ N : ℕ, n₀ ≤ N ∧
          ∃ Z : SimpleGraph (Fin N), ∃ side : Fin N → Bool,
            (∀ u v : Fin N, Z.Adj u v → side u ≠ side v) ∧
            (∀ v : Fin N, side v = true → Z.degree v = 2 * d₁) ∧
            (∀ v : Fin N, side v = false → Z.degree v = 2 * d₂) ∧
            HasExpansionProfileAtLeast (fun v => Z.neighborFinset v)
              (N / d₁ ^ 3) (δ * (d₁ : ℝ)) := by
  sorry
