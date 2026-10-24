import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

namespace LosslessVertexExpander

open Finset

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- `N(S)`, the neighbourhood of a set of left vertices. -/
def nbhd (nbr : L → Finset R) (S : Finset L) : Finset R :=
  S.biUnion nbr

/-- The vertices of `S` adjacent to a given right vertex `v`. -/
def fibre (nbr : L → Finset R) (S : Finset L) (v : R) : Finset L :=
  S.filter fun u => v ∈ nbr u

/-- `UN(S)`, the set of unique neighbours of `S`: right vertices with exactly
one edge to `S` (footnote 1 of the paper). -/
def uniqueNeighbours (nbr : L → Finset R) (S : Finset L) : Finset R :=
  (nbhd nbr S).filter fun v => (fibre nbr S v).card = 1

omit [DecidableEq L] in
/-- Unique neighbours of `S` are neighbours of `S`. -/
theorem uniqueNeighbours_subset (nbr : L → Finset R) (S : Finset L) :
    uniqueNeighbours nbr S ⊆ nbhd nbr S :=
  Finset.filter_subset _ _

omit [DecidableEq L] in
/-- Every vertex of `N(S)` has at least one neighbour in `S`. -/
theorem one_le_card_fibre (nbr : L → Finset R) {S : Finset L} {v : R}
    (hv : v ∈ nbhd nbr S) : 1 ≤ (fibre nbr S v).card := by
  rw [nbhd, Finset.mem_biUnion] at hv
  obtain ⟨u, hu, hvu⟩ := hv
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  simp only [fibre, Finset.mem_filter]
  exact ⟨hu, hvu⟩

omit [DecidableEq L] in
/-- Double counting the edges leaving `S`. -/
theorem sum_card_nbr_eq_sum_card_fibre (nbr : L → Finset R) (S : Finset L)
    (N : Finset R) (hsub : ∀ u ∈ S, nbr u ⊆ N) :
    ∑ u ∈ S, (nbr u).card = ∑ v ∈ N, (fibre nbr S v).card := by
  have hleft : ∀ u ∈ S, (nbr u).card = ∑ v ∈ N, (if v ∈ nbr u then 1 else 0) := by
    intro u hu
    have hfil : (N.filter fun v => v ∈ nbr u) = nbr u := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub u hu h, h⟩⟩
    calc (nbr u).card = (N.filter fun v => v ∈ nbr u).card := by rw [hfil]
      _ = ∑ v ∈ N, (if v ∈ nbr u then 1 else 0) := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hright : ∀ v ∈ N, (fibre nbr S v).card = ∑ u ∈ S, (if v ∈ nbr u then 1 else 0) := by
    intro v _
    rw [fibre, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright, Finset.sum_comm]

omit [DecidableEq L] in
/-- The edge count behind footnote 1: `2 |N(S)|` is at most `|UN(S)|` plus the
number of edges leaving `S`. -/
theorem two_mul_card_nbhd_le (nbr : L → Finset R) (S : Finset L) :
    2 * (nbhd nbr S).card ≤ (uniqueNeighbours nbr S).card + ∑ u ∈ S, (nbr u).card := by
  classical
  set N := nbhd nbr S with hN
  set p : R → Prop := fun v => (fibre nbr S v).card = 1 with hp
  have hsub : ∀ u ∈ S, nbr u ⊆ N := fun u hu => Finset.subset_biUnion_of_mem nbr hu
  have hcount := sum_card_nbr_eq_sum_card_fibre nbr S N hsub
  -- split the right degrees into the unique neighbours and the rest
  have hsplit : ∑ v ∈ N, (fibre nbr S v).card
      = ∑ v ∈ N.filter p, (fibre nbr S v).card
        + ∑ v ∈ N.filter (fun v => ¬ p v), (fibre nbr S v).card :=
    (Finset.sum_filter_add_sum_filter_not N p _).symm
  have hone : ∑ v ∈ N.filter p, (fibre nbr S v).card = (N.filter p).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl ?_
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have htwo : 2 * (N.filter (fun v => ¬ p v)).card
      ≤ ∑ v ∈ N.filter (fun v => ¬ p v), (fibre nbr S v).card := by
    have hge : ∀ v ∈ N.filter (fun v => ¬ p v), 2 ≤ (fibre nbr S v).card := by
      intro v hv
      obtain ⟨hvN, hvp⟩ := Finset.mem_filter.mp hv
      have h1 := one_le_card_fibre nbr (hN ▸ hvN)
      have h2 : (fibre nbr S v).card ≠ 1 := hvp
      omega
    have h := Finset.card_nsmul_le_sum (N.filter (fun v => ¬ p v))
      (fun v => (fibre nbr S v).card) 2 hge
    simpa [smul_eq_mul, mul_comm] using h
  have hcard : (N.filter p).card + (N.filter (fun v => ¬ p v)).card = N.card :=
    Finset.card_filter_add_card_filter_not _
  have hU : uniqueNeighbours nbr S = N.filter p := rfl
  rw [hU]
  omega

omit [DecidableEq L] in
/-- **Footnote 1 of the paper.**  If every left vertex of `S` has degree `d` and
`S` expands losslessly, `|N(S)| >= (1 - eps) d |S|`, then `S` has at least
`(1 - 2 eps) d |S|` unique neighbours. -/
theorem uniqueNeighbourExpansion_of_vertexExpansion (nbr : L → Finset R) (d : ℕ)
    (eps : ℝ) (S : Finset L) (hreg : ∀ u ∈ S, (nbr u).card = d)
    (hexp : (1 - eps) * (d * S.card) ≤ ((nbhd nbr S).card : ℝ)) :
    (1 - 2 * eps) * (d * S.card) ≤ ((uniqueNeighbours nbr S).card : ℝ) := by
  have hdeg : ∑ u ∈ S, (nbr u).card = d * S.card := by
    rw [Finset.sum_congr rfl hreg, Finset.sum_const, smul_eq_mul, mul_comm]
  have hkey := two_mul_card_nbhd_le nbr S
  rw [hdeg] at hkey
  have hcast : (2 : ℝ) * ((nbhd nbr S).card : ℝ)
      ≤ ((uniqueNeighbours nbr S).card : ℝ) + (d : ℝ) * (S.card : ℝ) := by
    exact_mod_cast hkey
  nlinarith [hcast, hexp]

/-- Definition 2.1, left half: every set of left vertices of density at most
`delta` has at least `alpha * dL * |S|` neighbours on the right. -/
def LeftVertexExpander [Fintype L] (nbr : L → Finset R) (dL : ℕ) (alpha delta : ℝ) : Prop :=
  ∀ S : Finset L, (S.card : ℝ) ≤ delta * (Fintype.card L : ℝ) →
    alpha * (dL * S.card) ≤ ((nbhd nbr S).card : ℝ)

/-- Definition 2.1: a two-sided `alpha`-vertex expander, described by the two
neighbourhood functions of a bipartite graph.  Taking `alpha = 1 - o_d(1)` gives
the paper's notion of a two-sided lossless expander. -/
def TwoSidedVertexExpander [Fintype L] [Fintype R] (nbrL : L → Finset R)
    (nbrR : R → Finset L) (dL dR : ℕ) (alpha delta : ℝ) : Prop :=
  LeftVertexExpander nbrL dL alpha delta ∧ LeftVertexExpander nbrR dR alpha delta

/-- The unique-neighbour counterpart of `LeftVertexExpander` (footnote 1 of the
paper): every set of left vertices of density at most `delta` has at least
`alpha * dL * |S|` unique neighbours on the right. -/
def LeftUniqueNeighbourExpander [Fintype L] (nbr : L → Finset R) (dL : ℕ)
    (alpha delta : ℝ) : Prop :=
  ∀ S : Finset L, (S.card : ℝ) ≤ delta * (Fintype.card L : ℝ) →
    alpha * (dL * S.card) ≤ ((uniqueNeighbours nbr S).card : ℝ)

omit [DecidableEq L] in
/-- **Footnote 1** in the language of Definition 2.1: a `d`-left-regular
`(1 - eps)`-vertex expander is a `(1 - 2 eps)`-unique-neighbour expander with
the same density threshold. -/
theorem leftUniqueNeighbourExpander_of_leftVertexExpander [Fintype L]
    (nbr : L → Finset R) (d : ℕ) (eps delta : ℝ) (hreg : ∀ u, (nbr u).card = d)
    (h : LeftVertexExpander nbr d (1 - eps) delta) :
    LeftUniqueNeighbourExpander nbr d (1 - 2 * eps) delta :=
  fun S hS =>
    uniqueNeighbourExpansion_of_vertexExpansion nbr d eps S (fun u _ => hreg u) (h S hS)

/-- The introduction's notion of vertex expansion for an ordinary graph on `V`
presented by its neighbourhood function: every `S ⊆ V` with `|S| <= eta |V|`
has at least `gamma * d * |S|` distinct neighbours. -/
def IsVertexExpander {V : Type*} [Fintype V] [DecidableEq V] (nbr : V → Finset V)
    (d : ℕ) (gamma eta : ℝ) : Prop :=
  ∀ S : Finset V, (S.card : ℝ) ≤ eta * (Fintype.card V : ℝ) →
    gamma * (d * S.card) ≤ ((nbhd nbr S).card : ℝ)

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The left neighbourhood function of the tripartite line product `(GL, GR) ⊗ H`
(Definition 2.4): `LNbr u` and `RNbr u` list the left and right neighbours of the
middle vertex `u`, and for each edge `(i, j)` of the gadget `hnbr` on `[DL] × [DR]`
the vertex `LNbr u i` is joined to `RNbr u j`. -/
def tripartiteLineProduct [Fintype R] {DL DR : ℕ} (LNbr : M → Fin DL → L)
    (RNbr : M → Fin DR → R) (hnbr : Fin DL → Finset (Fin DR)) (x : L) : Finset R :=
  Finset.univ.filter fun y : R =>
    ∃ u : M, ∃ i : Fin DL, ∃ j : Fin DR, LNbr u i = x ∧ RNbr u j = y ∧ j ∈ hnbr i

/-- The trace of `S` on the gadget copy sitting at the middle vertex `u`: the
indices `i` for which the `i`-th left neighbour of `u` lies in `S`. -/
def middleTrace {DL : ℕ} (LNbr : M → Fin DL → L) (S : Finset L) (u : M) :
    Finset (Fin DL) :=
  Finset.univ.filter fun i => LNbr u i ∈ S

/-- The neighbourhood of a set of gadget-left-indices inside the gadget. -/
def gadgetNbhd {DL DR : ℕ} (hnbr : Fin DL → Finset (Fin DR)) (A : Finset (Fin DL)) :
    Finset (Fin DR) :=
  A.biUnion hnbr

omit [DecidableEq M] in
/-- Definition 2.4, unfolded: in the tripartite line product, `N(S)` is the union
over the middle vertices `u` of the images under `RNbr u` of the gadget
neighbourhoods of the traces of `S` at `u`. -/
theorem nbhd_tripartiteLineProduct [Fintype R] {DL DR : ℕ} (LNbr : M → Fin DL → L)
    (RNbr : M → Fin DR → R) (hnbr : Fin DL → Finset (Fin DR)) (S : Finset L) :
    nbhd (tripartiteLineProduct LNbr RNbr hnbr) S
      = Finset.univ.biUnion fun u : M =>
          (gadgetNbhd hnbr (middleTrace LNbr S u)).image (RNbr u) := by
  classical
  ext y
  simp only [nbhd, Finset.mem_biUnion, tripartiteLineProduct, Finset.mem_filter,
    Finset.mem_univ, true_and, gadgetNbhd, middleTrace, Finset.mem_image]
  constructor
  · rintro ⟨x, hxS, u, i, j, hLx, hRy, hji⟩
    exact ⟨u, j, ⟨i, hLx ▸ hxS, hji⟩, hRy⟩
  · rintro ⟨u, j, ⟨i, hiS, hji⟩, hRy⟩
    exact ⟨LNbr u i, hiS, u, i, j, rfl, hRy, hji⟩

omit [DecidableEq M] in
/-- In the tripartite line product, `|N(S)|` is at most the sum over the middle
vertices `u` of the gadget neighbourhood sizes of the traces of `S` at `u`. -/
theorem card_nbhd_tripartiteLineProduct_le [Fintype R] {DL DR : ℕ}
    (LNbr : M → Fin DL → L) (RNbr : M → Fin DR → R)
    (hnbr : Fin DL → Finset (Fin DR)) (S : Finset L) :
    (nbhd (tripartiteLineProduct LNbr RNbr hnbr) S).card
      ≤ ∑ u : M, (gadgetNbhd hnbr (middleTrace LNbr S u)).card := by
  classical
  rw [nbhd_tripartiteLineProduct]
  refine (Finset.card_biUnion_le).trans ?_
  refine Finset.sum_le_sum ?_
  intro u _
  exact Finset.card_image_le

/-- A finite bipartite graph `(L, R, E)` with left side `L = Fin nL`, right
side `R = Fin nR` and edge relation `Adj`. -/
structure BipartiteGraph where
  /-- The number of left vertices. -/
  nL : ℕ
  /-- The number of right vertices. -/
  nR : ℕ
  /-- `Adj u v` holds exactly when `(u, v)` is an edge. -/
  Adj : Fin nL → Fin nR → Prop

namespace BipartiteGraph

open Classical in
/-- The neighbourhood function of the left side: `N(u) ⊆ R`. -/
noncomputable def leftNbr (G : BipartiteGraph) (u : Fin G.nL) : Finset (Fin G.nR) :=
  Finset.univ.filter fun v => G.Adj u v

open Classical in
/-- The neighbourhood function of the right side: `N(v) ⊆ L`. -/
noncomputable def rightNbr (G : BipartiteGraph) (v : Fin G.nR) : Finset (Fin G.nL) :=
  Finset.univ.filter fun u => G.Adj u v

/-- Membership in `leftNbr` is adjacency. -/
@[simp]
theorem mem_leftNbr {G : BipartiteGraph} {u : Fin G.nL} {v : Fin G.nR} :
    v ∈ G.leftNbr u ↔ G.Adj u v := by
  simp [leftNbr]

/-- Membership in `rightNbr` is adjacency. -/
@[simp]
theorem mem_rightNbr {G : BipartiteGraph} {u : Fin G.nL} {v : Fin G.nR} :
    u ∈ G.rightNbr v ↔ G.Adj u v := by
  simp [rightNbr]

/-- `G` is `(dL, dR)`-biregular: every left vertex has degree `dL` and every
right vertex has degree `dR`. -/
def IsBiregular (G : BipartiteGraph) (dL dR : ℕ) : Prop :=
  (∀ u : Fin G.nL, (G.leftNbr u).card = dL) ∧ ∀ v : Fin G.nR, (G.rightNbr v).card = dR

/-- Double counting the edges of a `(dL, dR)`-biregular graph:
`|L| * dL = |R| * dR`. -/
theorem nL_mul_eq_nR_mul {G : BipartiteGraph} {dL dR : ℕ} (h : G.IsBiregular dL dR) :
    G.nL * dL = G.nR * dR := by
  have hcount := sum_card_nbr_eq_sum_card_fibre G.leftNbr Finset.univ Finset.univ
    (fun _ _ => Finset.subset_univ _)
  have hfib : ∀ v : Fin G.nR, fibre G.leftNbr Finset.univ v = G.rightNbr v := by
    intro v
    ext u
    simp [fibre]
  have hL : ∑ u : Fin G.nL, (G.leftNbr u).card = G.nL * dL := by
    simp only [h.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hR : ∑ v : Fin G.nR, (fibre G.leftNbr Finset.univ v).card = G.nR * dR := by
    simp only [hfib, h.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact hL.symm.trans (hcount.trans hR)

/-- A `(d, d)`-biregular graph with `d > 0` has sides of equal size. -/
theorem nL_eq_nR {G : BipartiteGraph} {d : ℕ} (hd : 0 < d) (h : G.IsBiregular d d) :
    G.nL = G.nR :=
  Nat.eq_of_mul_eq_mul_right hd (nL_mul_eq_nR_mul h)

/-- The vertex set `L ⊔ R` of `G` viewed as an ordinary graph. -/
abbrev Vertex (G : BipartiteGraph) : Type := Fin G.nL ⊕ Fin G.nR

/-- `L ⊔ R` has `nL + nR` vertices. -/
theorem card_vertex (G : BipartiteGraph) : Fintype.card G.Vertex = G.nL + G.nR := by
  simp [Vertex]

/-- The neighbourhood function of `G` as an ordinary graph on `L ⊔ R`: a left
vertex sees its right neighbours and a right vertex sees its left neighbours. -/
noncomputable def nbr (G : BipartiteGraph) : Fin G.nL ⊕ Fin G.nR → Finset G.Vertex
  | Sum.inl u => (∅ : Finset (Fin G.nL)).disjSum (G.leftNbr u)
  | Sum.inr v => (G.rightNbr v).disjSum (∅ : Finset (Fin G.nR))

/-- `G` is `d`-regular as an ordinary graph on `L ⊔ R`. -/
def IsRegular (G : BipartiteGraph) (d : ℕ) : Prop :=
  ∀ x : G.Vertex, (G.nbr x).card = d

/-- A `(d, d)`-biregular graph is `d`-regular on `L ⊔ R`. -/
theorem isRegular_of_isBiregular {G : BipartiteGraph} {d : ℕ} (h : G.IsBiregular d d) :
    G.IsRegular d := by
  rintro (u | v)
  · simp [nbr, h.1 u]
  · simp [nbr, h.2 v]

/-- The ordinary simple graph on `L ⊔ R` underlying `G`. -/
def toSimpleGraph (G : BipartiteGraph) : SimpleGraph G.Vertex :=
  SimpleGraph.fromRel fun x y => ∃ u v, x = Sum.inl u ∧ y = Sum.inr v ∧ G.Adj u v

/-- `nbr` is the neighbourhood function of `toSimpleGraph`. -/
theorem mem_nbr_iff_adj (G : BipartiteGraph) (x y : G.Vertex) :
    y ∈ G.nbr x ↔ G.toSimpleGraph.Adj x y := by
  rcases x with u | v <;> rcases y with u' | v' <;>
    simp [nbr, toSimpleGraph, SimpleGraph.fromRel_adj]

/-- The neighbourhood of `S ⊆ L ⊔ R` in the ordinary graph is the disjoint
union of the left neighbourhood of `S ∩ R` and the right neighbourhood of
`S ∩ L`. -/
theorem nbhd_nbr (G : BipartiteGraph) (S : Finset G.Vertex) :
    nbhd G.nbr S = (nbhd G.rightNbr S.toRight).disjSum (nbhd G.leftNbr S.toLeft) := by
  ext (u | v)
  · simp only [nbhd, Finset.mem_biUnion, Finset.inl_mem_disjSum, Finset.mem_toRight]
    constructor
    · rintro ⟨x, hxS, hux⟩
      rcases x with u' | v'
      · simp [nbr] at hux
      · exact ⟨v', hxS, by simpa [nbr] using hux⟩
    · rintro ⟨v', hv'S, huv'⟩
      exact ⟨Sum.inr v', hv'S, by simpa [nbr] using huv'⟩
  · simp only [nbhd, Finset.mem_biUnion, Finset.inr_mem_disjSum, Finset.mem_toLeft]
    constructor
    · rintro ⟨x, hxS, hvx⟩
      rcases x with u' | v'
      · exact ⟨u', hxS, by simpa [nbr] using hvx⟩
      · simp [nbr] at hvx
    · rintro ⟨u', hu'S, hvu'⟩
      exact ⟨Sum.inl u', hu'S, by simpa [nbr] using hvu'⟩

/-- A `(d, d)`-biregular two-sided `gamma`-vertex expander with density threshold
`eta` is a `gamma`-vertex expander on `L ⊔ R` with threshold `eta / 2` (Section 1:
for `dL = dR` the two-sided notion recovers the usual one). -/
theorem isVertexExpander_of_twoSided (G : BipartiteGraph) {d : ℕ} (hd : 0 < d)
    (hreg : G.IsBiregular d d) {gamma eta : ℝ}
    (h : TwoSidedVertexExpander G.leftNbr G.rightNbr d d gamma eta) :
    IsVertexExpander G.nbr d gamma (eta / 2) := by
  intro S hS
  have hn : G.nL = G.nR := nL_eq_nR hd hreg
  have hnR : (G.nR : ℝ) = G.nL := by exact_mod_cast hn.symm
  have hcardV : (Fintype.card G.Vertex : ℝ) = (G.nL : ℝ) + (G.nR : ℝ) := by
    rw [card_vertex, Nat.cast_add]
  have hS' : (S.card : ℝ) ≤ eta * (G.nL : ℝ) := by
    rw [hcardV, hnR] at hS
    have : eta / 2 * ((G.nL : ℝ) + G.nL) = eta * G.nL := by ring
    linarith
  have hSL : (S.toLeft.card : ℝ) ≤ eta * (Fintype.card (Fin G.nL) : ℝ) := by
    rw [Fintype.card_fin]
    exact le_trans (by exact_mod_cast Finset.card_toLeft_le) hS'
  have hSR : (S.toRight.card : ℝ) ≤ eta * (Fintype.card (Fin G.nR) : ℝ) := by
    rw [Fintype.card_fin, hnR]
    exact le_trans (by exact_mod_cast Finset.card_toRight_le) hS'
  have hL := h.1 S.toLeft hSL
  have hR := h.2 S.toRight hSR
  have hsplit : ((nbhd G.nbr S).card : ℝ)
      = ((nbhd G.rightNbr S.toRight).card : ℝ) + ((nbhd G.leftNbr S.toLeft).card : ℝ) := by
    rw [nbhd_nbr, Finset.card_disjSum, Nat.cast_add]
  have hcardS : (S.card : ℝ) = (S.toLeft.card : ℝ) + (S.toRight.card : ℝ) := by
    exact_mod_cast (Finset.card_toLeft_add_card_toRight (u := S)).symm
  rw [hsplit, hcardS]
  linarith

end BipartiteGraph

/-- Definition 2.1 for a family `Z n` of bipartite graphs: there is one `eta > 0`,
uniform over the family, such that every `Z n` is a two-sided `gamma`-vertex
expander with degrees `dL, dR` and density threshold `eta`. -/
def IsTwoSidedVertexExpanderFamily (Z : ℕ → BipartiteGraph) (dL dR : ℕ) (gamma : ℝ) :
    Prop :=
  ∃ eta : ℝ, 0 < eta ∧
    ∀ n, TwoSidedVertexExpander (Z n).leftNbr (Z n).rightNbr dL dR gamma eta

/-- The family `Z n` has `Θ(n)` vertices: `|L_n| + |R_n| = Θ(n)` as `n → ∞`.
In particular the family is infinite. -/
def HasThetaNVertices (Z : ℕ → BipartiteGraph) : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (((Z n).nL + (Z n).nR : ℕ) : ℝ))
    fun n : ℕ => (n : ℝ)

end LosslessVertexExpander

open LosslessVertexExpander in
/-- Theorem 2.2 of Hsieh–Lubotzky–Mohanty–Reiner–Zhang, arXiv:2504.15087, existence only (the
paper's polynomial-time algorithm is not asserted): for `eps ∈ (0, 1]` there is `k`, and for each
`beta ∈ (0, 1]` a `d₀`, such that for `d₀ ≤ dL, dR` with `beta ≤ dL / dR ≤ beta + eps` some family
of `(k dL, k dR)`-biregular graphs on `Θ(n)` vertices is a two-sided `(1 - eps)`-vertex expander. -/
theorem P094 {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ k : ℕ, 0 < k ∧ ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      ∃ d₀ : ℕ, 0 < d₀ ∧
        ∀ dL dR : ℕ, d₀ ≤ dL → d₀ ≤ dR →
          beta * (dR : ℝ) ≤ (dL : ℝ) → (dL : ℝ) ≤ (beta + eps) * (dR : ℝ) →
          ∃ Z : ℕ → BipartiteGraph,
            (∀ n, (Z n).IsBiregular (k * dL) (k * dR)) ∧
            HasThetaNVertices Z ∧
            IsTwoSidedVertexExpanderFamily Z (k * dL) (k * dR) (1 - eps) := by
  sorry

namespace LosslessVertexExpander

open Finset

/-- Theorem 1 of the paper for degrees divisible by `k` (the case `beta = 1`, `dL = dR` of
Theorem 2.2): for `eps ∈ (0, 1]` there are `k > 0` and `d₀` such that for every `d ≥ d₀` some
family of `k d`-regular graphs on `Θ(n)` vertices consists of `(1 - eps)`-vertex expanders.
The extension to every degree `d ≥ d₀` (Remark 2.3) is not formalised. -/
theorem kd_regular_lossless_expanders_exist {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ d₀ : ℕ, 0 < d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ Z : ℕ → BipartiteGraph,
        (∀ n, (Z n).IsRegular (k * d)) ∧ HasThetaNVertices Z ∧
        ∃ eta : ℝ, 0 < eta ∧ ∀ n, IsVertexExpander (Z n).nbr (k * d) (1 - eps) eta := by
  obtain ⟨k, hk, hmain⟩ := P094 heps0 heps1
  obtain ⟨d₀, hd₀, hfam⟩ := hmain 1 one_pos le_rfl
  refine ⟨k, hk, d₀, hd₀, fun d hd => ?_⟩
  have hd_pos : 0 < d := lt_of_lt_of_le hd₀ hd
  have hlo : (1 : ℝ) * (d : ℝ) ≤ (d : ℝ) := by rw [one_mul]
  have hhi : (d : ℝ) ≤ (1 + eps) * (d : ℝ) := by
    have := mul_nonneg heps0.le (Nat.cast_nonneg d)
    linarith
  obtain ⟨Z, hbireg, htheta, hexp⟩ := hfam d d hd hd hlo hhi
  obtain ⟨eta, heta, hexp⟩ := hexp
  refine ⟨Z, fun n => BipartiteGraph.isRegular_of_isBiregular (hbireg n), htheta,
    eta / 2, half_pos heta, fun n => ?_⟩
  exact BipartiteGraph.isVertexExpander_of_twoSided (Z n) (mul_pos hk hd_pos) (hbireg n)
    (hexp n)

/-- Theorem 2.2 combined with footnote 1: the families of Theorem 2.2 are two-sided
`(1 - 2 eps)`-unique-neighbour expanders. -/
theorem twoSided_uniqueNeighbour_expanders_exist {eps : ℝ} (heps0 : 0 < eps)
    (heps1 : eps ≤ 1) :
    ∃ k : ℕ, 0 < k ∧ ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      ∃ d₀ : ℕ, 0 < d₀ ∧
        ∀ dL dR : ℕ, d₀ ≤ dL → d₀ ≤ dR →
          beta * (dR : ℝ) ≤ (dL : ℝ) → (dL : ℝ) ≤ (beta + eps) * (dR : ℝ) →
          ∃ Z : ℕ → BipartiteGraph,
            (∀ n, (Z n).IsBiregular (k * dL) (k * dR)) ∧
            HasThetaNVertices Z ∧
            ∃ eta : ℝ, 0 < eta ∧ ∀ n,
              LeftUniqueNeighbourExpander (Z n).leftNbr (k * dL) (1 - 2 * eps) eta ∧
              LeftUniqueNeighbourExpander (Z n).rightNbr (k * dR) (1 - 2 * eps) eta := by
  obtain ⟨k, hk, hmain⟩ := P094 heps0 heps1
  refine ⟨k, hk, fun beta hbeta0 hbeta1 => ?_⟩
  obtain ⟨d₀, hd₀, hfam⟩ := hmain beta hbeta0 hbeta1
  refine ⟨d₀, hd₀, fun dL dR hdL hdR hlo hhi => ?_⟩
  obtain ⟨Z, hbireg, htheta, hexp⟩ := hfam dL dR hdL hdR hlo hhi
  obtain ⟨eta, heta, hexp⟩ := hexp
  refine ⟨Z, hbireg, htheta, eta, heta, fun n => ⟨?_, ?_⟩⟩
  · exact leftUniqueNeighbourExpander_of_leftVertexExpander _ _ eps eta (hbireg n).1
      (hexp n).1
  · exact leftUniqueNeighbourExpander_of_leftVertexExpander _ _ eps eta (hbireg n).2
      (hexp n).2

end LosslessVertexExpander
