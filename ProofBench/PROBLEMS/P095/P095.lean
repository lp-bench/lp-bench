import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace TwoSidedUniqueNeighbour

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : SimpleGraph V) [DecidableRel F.Adj]

/-- The number of ordered adjacent pairs in `s × t`: `2 e(s)` for `s = t`, and the
paper's `e(s, t)` for disjoint `s` and `t`. -/
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

/-- The vertices of degree at most `2 * gamma`. -/
noncomputable def lowDegree (gamma : ℝ) : Finset V :=
  Finset.univ.filter fun v => (F.degree v : ℝ) ≤ 2 * gamma

/-- The vertices of degree more than `2 * gamma`. -/
noncomputable def highDegree (gamma : ℝ) : Finset V :=
  Finset.univ.filter fun v => ¬ ((F.degree v : ℝ) ≤ 2 * gamma)

omit [DecidableEq V] in
/-- Low- and high-degree vertices are disjoint. -/
theorem disjoint_lowDegree_highDegree (gamma : ℝ) :
    Disjoint (lowDegree F gamma) (highDegree F gamma) :=
  Finset.disjoint_filter_filter_not _ _ _

/-- Every vertex has low or high degree. -/
theorem lowDegree_union_highDegree (gamma : ℝ) :
    lowDegree F gamma ∪ highDegree F gamma = Finset.univ :=
  Finset.filter_union_filter_not_eq _ _

omit [DecidableEq V] in
/-- A high-degree vertex has degree more than `2 * gamma`. -/
theorem two_mul_gamma_lt_degree_of_mem_highDegree {gamma : ℝ} {v : V}
    (hv : v ∈ highDegree F gamma) : 2 * gamma < (F.degree v : ℝ) :=
  not_le.mp (Finset.mem_filter.mp hv).2

omit [DecidableEq V] in
/-- Lemma 2.2 of the paper: if `2 e(S) ≤ gamma |S|` for every vertex set `S`, then
`2 e(F)` is at most three times the sum of the degrees of the vertices of degree at
most `2 gamma`. -/
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

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq E]

/-- The neighbourhood function of the line product `G ⊗ H` (Definition 3.1) of a
`D`-regular graph `G` with a gadget `H` on `[D]`: the vertices are the edges of `G`,
`inc v i` is the `i`-th edge at `v`, and a copy of `H` sits on the edges at each `v`. -/
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

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `UN(S)`, the unique neighbours of `S` for a graph presented by a
neighbourhood function: the vertices with exactly one neighbour in `S`. -/
def uniqueNeighbours {β : Type*} [Fintype β] [DecidableEq β] (nbr : α → Finset β)
    (S : Finset α) : Finset β :=
  Finset.univ.filter fun v => (S.filter fun u => v ∈ nbr u).card = 1

/-- Definition 3.2: the statement `P_H(t) >= c` for the unique-neighbour
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

/-- Definition 1.1 (as encoded here): a bipartite graph, given by the neighbourhood
functions of its sides, in which every left set of density below `delta` has at
least `alpha d1 |S|` neighbours, and symmetrically on the right with `d2`. -/
def TwoSidedUniqueNeighbourExpander {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R] (nbrL : L → Finset R) (nbrR : R → Finset L)
    (d1 d2 : ℕ) (alpha delta : ℝ) : Prop :=
  (∀ S : Finset L, (S.card : ℝ) < delta * (Fintype.card L : ℝ) →
      alpha * (d1 * S.card) ≤ ((nbhd nbrL S).card : ℝ)) ∧
    (∀ S : Finset R, (S.card : ℝ) < delta * (Fintype.card R : ℝ) →
      alpha * (d2 * S.card) ≤ ((nbhd nbrR S).card : ℝ))

end TwoSidedUniqueNeighbour

open TwoSidedUniqueNeighbour in
open scoped Classical in
/-- Theorem 4.4 (formal version of Theorem 1.2) of Hsieh–McKenzie–Mohanty–Paredes,
arXiv:2302.01212: for `β ∈ (0, 1/2]` there are `d₀, δ > 0` such that for even `d₁, d₂ ≥ d₀`
with `β/(1-β) ≤ d₁/d₂ ≤ 1` there are arbitrarily large `(2d₁, 2d₂)`-biregular bipartite
graphs whose vertex sets `S` of size at most `N / d₁³` have `≥ δ d₁ |S|` unique neighbours. -/
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
