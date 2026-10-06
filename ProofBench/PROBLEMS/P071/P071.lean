import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/- ---------------------------------------------------- -/
/- Paper: Bipartite Unique-Neighbour Expanders via Ramanujan Graphs -/
/- ---------------------------------------------------- -/

/-!
# P071: Bipartite unique-neighbour expanders via Ramanujan graphs

This file formalizes the combinatorial core and the main theorem of

  R. Asherov and I. Dinur, *Bipartite unique-neighbour expanders via Ramanujan
  graphs*, arXiv:2301.03072.

## The paper's dependency graph

The dependency graph for Theorem 1 is:

* Section 3.1: bipartite neighbourhoods `N(S)`, unique neighbours, and the
  various notions of expansion;
* Theorem 3 (quoted from Ballantine et al.): explicit `(q+1, q^3+1)`-biregular
  Ramanujan graphs;
* Theorem 2: the average right-degree bound
  `c|S| / |N(S)| <= 1 + (1+eps) * sqrt((d-1)/(c-1))` for biregular Ramanujan
  graphs, proved by counting non-backtracking paths (Lemmas 7-10);
* Lemma 11: existence of a fixed-size gadget with the unique-neighbour
  property, by the probabilistic method;
* Section 6.1: the *routed product* `G (x) G0`;
* Lemma 12: unique neighbours are inherited from the gadget by the routed
  product;
* Section 6.2: Theorem 1, obtained by combining Theorem 2, Lemma 11 and
  Lemma 12.

## What is formalized here

The target of the problem is the paper's main theorem, **Theorem 1**, stated
at the end of this file as `bipartite_uniqueNeighbour_expanders_exist` and
proved by `sorry`, the single `sorry` of the file.  Everything else below is
proved from first principles with no `sorry` and no new axioms:

* `exists_uniqueNeighbour_of_card_lt`, the counting argument recorded in
  Section 2 ("if a set expands by a factor of more than `c/2`, then it has
  unique neighbours"), which is what makes lossless expanders
  unique-neighbour expanders;
* `routedProduct`, the definition of Section 6.1;
* `card_filter_routedProduct_eq_one`, which is **Lemma 12**;
* `exists_uniqueNeighbour_routedProduct`, which is the final assembly step of
  Section 6.2: a right vertex of small induced degree together with a good
  gadget produces a unique neighbour in the routed product;
* `BipartiteMultigraph`, `BipartiteMultigraph.IsBiregular` and
  `IsUniqueNeighbourExpanderFamily`: the objects of Section 1 and Section 3.1
  in which Theorem 1 is phrased.

## What is deliberately not asserted

* The clause "polynomial-time construction" of Theorem 1 (and the word
  *explicit* in Theorem 3): these are statements about a model of computation
  and are not expressible in the present development.  Only the existence of
  the family and its expansion are stated.
* Theorem 2 (spectral, via non-backtracking path counts) and Lemma 11 (a
  probabilistic existence statement).  Theorem 1 is exactly
  `exists_uniqueNeighbour_routedProduct` fed with those two inputs; the upper
  layer `P071_UB.lean` records that derivation.
* The proof of Section 6.2 takes a gadget with `R0 = (q^3+1) / (alpha (q+1))`
  right vertices, so it tacitly needs this number to be an integer, a proviso
  that the printed statement of Theorem 1 does not include.  The statement is
  formalized as printed; the proviso appears only in the gadget hypothesis of
  `P071_UB.lean`.

A bipartite graph is presented, as in the paper, by the neighbourhood function
of its left side: `nbr u` is the set of right vertices adjacent to `u`.  Since
`N(S)` and "unique neighbour" only ever refer to the underlying simple
incidence structure, no multiplicities are lost; degrees, which do count
parallel edges, are handled by `BipartiteMultigraph` below.
-/

namespace RamanujanRoutedProduct

open Finset

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-! ## Bipartite neighbourhoods and unique neighbours -/

/-- `N(S)`: the neighbourhood of a set `S` of left vertices. -/
def nbhd (nbr : L → Finset R) (S : Finset L) : Finset R :=
  S.biUnion nbr

/-- The fibre of a right vertex `v` over `S`: the vertices of `S` adjacent to
`v`.  Its cardinality is the degree of `v` in the subgraph induced by
`S` and `N(S)`. -/
def fibre (nbr : L → Finset R) (S : Finset L) (v : R) : Finset L :=
  S.filter fun u => v ∈ nbr u

/-- `v` is a *unique neighbour* of `S` when exactly one vertex of `S` is
adjacent to `v` (Section 3.1). -/
def IsUniqueNeighbour (nbr : L → Finset R) (S : Finset L) (v : R) : Prop :=
  (fibre nbr S v).card = 1

/-- A bipartite graph is left-`c`-regular when every left vertex has exactly
`c` neighbours; for a `(c, d)`-biregular graph this is the left condition. -/
def LeftRegular (nbr : L → Finset R) (c : ℕ) : Prop :=
  ∀ u : L, (nbr u).card = c

/-- The unique-neighbour property of a fixed-size gadget: every nonempty set of
at most `t` left vertices admits a unique neighbour.  This is the conclusion of
Lemma 11. -/
def HasUniqueNeighbourProperty (nbr : L → Finset R) (t : ℕ) : Prop :=
  ∀ S : Finset L, S.Nonempty → S.card ≤ t → ∃ v : R, IsUniqueNeighbour nbr S v

/-! ## Double counting in the induced subgraph -/

omit [DecidableEq L] in
/-- Double counting of the edges leaving `S`: summing the left degrees is the
same as summing the induced right degrees over any set `N` containing `N(S)`.
This is the identity behind the phrase "the total number of edges in the
induced subgraph is `c|S|`" in Section 4. -/
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
/-- Every vertex of `N(S)` has at least one neighbour in `S`. -/
theorem one_le_card_fibre (nbr : L → Finset R) {S : Finset L} {v : R}
    (hv : v ∈ nbhd nbr S) : 1 ≤ (fibre nbr S v).card := by
  rw [nbhd, Finset.mem_biUnion] at hv
  obtain ⟨u, hu, hvu⟩ := hv
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  simp only [fibre, Finset.mem_filter]
  exact ⟨hu, hvu⟩

/-! ## Expansion beyond `c/2` forces unique neighbours

This is the counting argument recorded in Section 2 of the paper: a bipartite
graph whose small sets expand by more than a factor `c/2` is automatically a
unique-neighbour expander.  It is the reason lossless expanders are
unique-neighbour expanders. -/

omit [DecidableEq L] in
/-- If the left degrees on `S` all equal `c` and `S` expands by strictly more
than a factor of `c/2`, then `S` has a unique neighbour. -/
theorem exists_uniqueNeighbour_of_card_lt (nbr : L → Finset R) (c : ℕ)
    (S : Finset L) (hreg : ∀ u ∈ S, (nbr u).card = c)
    (hexp : c * S.card < 2 * (nbhd nbr S).card) :
    ∃ v ∈ nbhd nbr S, IsUniqueNeighbour nbr S v := by
  by_contra hcon
  have hge : ∀ v ∈ nbhd nbr S, 2 ≤ (fibre nbr S v).card := by
    intro v hv
    have h1 := one_le_card_fibre nbr hv
    have h2 : (fibre nbr S v).card ≠ 1 := fun h => hcon ⟨v, hv, h⟩
    omega
  have hsub : ∀ u ∈ S, nbr u ⊆ nbhd nbr S := fun u hu =>
    Finset.subset_biUnion_of_mem nbr hu
  have hcount := sum_card_nbr_eq_sum_card_fibre nbr S (nbhd nbr S) hsub
  have hleft : ∑ u ∈ S, (nbr u).card = c * S.card := by
    rw [Finset.sum_congr rfl hreg, Finset.sum_const, smul_eq_mul, mul_comm]
  have hright : 2 * (nbhd nbr S).card ≤ ∑ v ∈ nbhd nbr S, (fibre nbr S v).card := by
    have h := Finset.card_nsmul_le_sum (nbhd nbr S) (fun v => (fibre nbr S v).card) 2 hge
    simpa [smul_eq_mul, mul_comm] using h
  omega

/-! ## The routed product (Section 6.1)

Following the paper, the big `(c, d)`-biregular graph `G = (L ∪ R, E)` is
presented through the function `E : R × [d] → L` sending a right vertex `v` and
an index `i` to the `i`-th neighbour of `v`.  The gadget `G0` is a bipartite
graph whose left side is `[d] = Fin d` and whose right side is `R0`; it is given
by its left neighbourhood function `gnbr : Fin d → Finset R0`.

The routed product `G (x) G0` has left side `L`, right side `R × R0`, and an
edge between `E v i` and `(v, j)` for every edge `(i, j)` of `G0`. -/

variable {R₀ : Type*} [DecidableEq R₀] [Fintype R₀]

/-- The indexed neighbours of `v` that lie in `S`; the set written `S'` in
Lemma 12. -/
def gadgetTrace {d : ℕ} (Ed : R → Fin d → L) (S : Finset L) (v : R) : Finset (Fin d) :=
  Finset.univ.filter fun i => Ed v i ∈ S

/-- The routed product `G (x) G0` of Section 6.1, given by the left
neighbourhood function of its left side `L`.  A left vertex `x` is joined to
`(v, j)` exactly when `x` is the `i`-th neighbour of `v` for some index `i`
adjacent to `j` in the gadget. -/
def routedProduct {d : ℕ} [Fintype R] (Ed : R → Fin d → L)
    (gnbr : Fin d → Finset R₀) (x : L) : Finset (R × R₀) :=
  Finset.univ.filter fun p => ∃ i : Fin d, Ed p.1 i = x ∧ p.2 ∈ gnbr i

omit [DecidableEq R] in
@[simp]
theorem mem_routedProduct {d : ℕ} [Fintype R] (Ed : R → Fin d → L)
    (gnbr : Fin d → Finset R₀) (x : L) (p : R × R₀) :
    p ∈ routedProduct Ed gnbr x ↔ ∃ i : Fin d, Ed p.1 i = x ∧ p.2 ∈ gnbr i := by
  classical
  simp [routedProduct]

/-- **Lemma 12.**  Let `S` be a set of left vertices and `v` a right vertex of
the big graph, and let `gadgetTrace` be the set `S'` of indices of `v` whose
neighbour lies in `S`.  If `j` is a unique neighbour of `S'` inside the gadget,
then `(v, j)` is a unique neighbour of `S` in the routed product. -/
theorem card_filter_routedProduct_eq_one {d : ℕ} [Fintype R]
    (Ed : R → Fin d → L) (gnbr : Fin d → Finset R₀) (S : Finset L) (v : R)
    (j : R₀) (hj : IsUniqueNeighbour gnbr (gadgetTrace Ed S v) j) :
    IsUniqueNeighbour (routedProduct Ed gnbr) S (v, j) := by
  classical
  have hj' : (fibre gnbr (gadgetTrace Ed S v) j).card = 1 := hj
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hj'
  have hmem : ∀ i : Fin d, (Ed v i ∈ S ∧ j ∈ gnbr i) ↔ i = i₀ := by
    intro i
    have hiff : i ∈ fibre gnbr (gadgetTrace Ed S v) j ↔ (Ed v i ∈ S ∧ j ∈ gnbr i) := by
      simp only [fibre, Finset.mem_filter, gadgetTrace, Finset.mem_univ, true_and]
    rw [← hiff, hi₀, Finset.mem_singleton]
  have hi₀S : Ed v i₀ ∈ S := ((hmem i₀).mpr rfl).1
  have hi₀j : j ∈ gnbr i₀ := ((hmem i₀).mpr rfl).2
  have hfib : fibre (routedProduct Ed gnbr) S (v, j) = {Ed v i₀} := by
    ext x
    simp only [fibre, Finset.mem_filter, Finset.mem_singleton, mem_routedProduct]
    constructor
    · rintro ⟨hxS, i, hEi, hji⟩
      have hpair : Ed v i ∈ S ∧ j ∈ gnbr i := ⟨hEi ▸ hxS, hji⟩
      have hii : i = i₀ := (hmem i).mp hpair
      subst hii
      exact hEi.symm
    · rintro rfl
      exact ⟨hi₀S, ⟨i₀, rfl, hi₀j⟩⟩
  rw [IsUniqueNeighbour, hfib, Finset.card_singleton]

/-- **The assembly step of Section 6.2.**  Suppose the gadget has the
unique-neighbour property up to size `t` (Lemma 11), and suppose the big graph
supplies a right vertex `v` whose induced degree in `S` is nonzero and at most
`t`.  This last hypothesis is what Theorem 2 provides: the average induced
right degree is at most `1 + (1+eps) * sqrt((d-1)/(c-1)) = 1 + (1+eps) q`,
which is below `q + 1` once `eps < 1/q`, so some right vertex has induced
degree at most `q + 1 = t`.  Then `S` has a unique neighbour in the routed
product, which is the conclusion of Theorem 1. -/
theorem exists_uniqueNeighbour_routedProduct {d t : ℕ} [Fintype R]
    (Ed : R → Fin d → L) (gnbr : Fin d → Finset R₀)
    (hgadget : HasUniqueNeighbourProperty gnbr t) (S : Finset L) (v : R)
    (hne : (gadgetTrace Ed S v).Nonempty) (hsmall : (gadgetTrace Ed S v).card ≤ t) :
    ∃ w : R × R₀, IsUniqueNeighbour (routedProduct Ed gnbr) S w := by
  obtain ⟨j, hj⟩ := hgadget (gadgetTrace Ed S v) hne hsmall
  exact ⟨(v, j), card_filter_routedProduct_eq_one Ed gnbr S v j hj⟩

/-! ## Bipartite multigraphs and biregularity (Section 3.1)

Section 3.1 works with graphs that may contain parallel edges but no loops,
Lemma 11 explicitly allows parallel edges in the gadget, and the routed
product inherits them.  A finite bipartite multigraph is therefore recorded by
the sizes of its two sides and the number `mult u v` of edges between `u` and
`v`.  Degrees count parallel edges, while `N(S)` and unique neighbours only see
the underlying incidence structure `nbr`, exactly as in Section 3.1. -/

/-- A finite bipartite multigraph `(L ⊔ R, E)` with left side `L = Fin nL`,
right side `R = Fin nR` and `mult u v` parallel edges between `u ∈ L` and
`v ∈ R`. -/
structure BipartiteMultigraph where
  /-- The number of left vertices `|L|`. -/
  nL : ℕ
  /-- The number of right vertices `|R|`. -/
  nR : ℕ
  /-- The number of edges between a left vertex and a right vertex. -/
  mult : Fin nL → Fin nR → ℕ

namespace BipartiteMultigraph

/-- The neighbourhood function of the left side: `v ∈ nbr u` exactly when
there is at least one edge between `u` and `v`. -/
def nbr (G : BipartiteMultigraph) (u : Fin G.nL) : Finset (Fin G.nR) :=
  Finset.univ.filter fun v => 0 < G.mult u v

@[simp]
theorem mem_nbr {G : BipartiteMultigraph} {u : Fin G.nL} {v : Fin G.nR} :
    v ∈ G.nbr u ↔ 0 < G.mult u v := by
  simp [nbr]

/-- The degree of a left vertex, counting parallel edges. -/
def leftDegree (G : BipartiteMultigraph) (u : Fin G.nL) : ℕ :=
  ∑ v, G.mult u v

/-- The degree of a right vertex, counting parallel edges. -/
def rightDegree (G : BipartiteMultigraph) (v : Fin G.nR) : ℕ :=
  ∑ u, G.mult u v

/-- `G` is `(c, d)`-biregular (Section 3.1): every left vertex has degree `c`
and every right vertex has degree `d`, parallel edges counted. -/
def IsBiregular (G : BipartiteMultigraph) (c d : ℕ) : Prop :=
  (∀ u, G.leftDegree u = c) ∧ ∀ v, G.rightDegree v = d

end BipartiteMultigraph

/-- **Section 1.**  A family `G n` of `(c, d)`-biregular bipartite graphs with
`|L_n| + |R_n| → ∞` is a *unique neighbour expander family* if there is
`δ > 0` such that for every `n` and every set of left vertices `S ⊆ L_n` of
size `|S| ≤ δ |L_n|` there is a unique neighbour of `S` in `G n`.  The sets
`S` are required to be nonempty, since the empty set has no unique
neighbour. -/
def IsUniqueNeighbourExpanderFamily (G : ℕ → BipartiteMultigraph) (c d : ℕ) : Prop :=
  (∀ n, (G n).IsBiregular c d) ∧
    Filter.Tendsto (fun n => (G n).nL + (G n).nR) Filter.atTop Filter.atTop ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ S : Finset (Fin (G n).nL), S.Nonempty →
      (S.card : ℝ) ≤ δ * ((G n).nL : ℝ) → ∃ v, IsUniqueNeighbour (G n).nbr S v

/-! ## Theorem 1: the main theorem -/

end RamanujanRoutedProduct

open RamanujanRoutedProduct in
/-- **Theorem 1** -- the main theorem of the paper.  There is a function
`q̂ : ℕ × ℝ → ℕ` such that for every integer `c₀ > 5` and real number
`α > 1`, if `q > q̂(c₀, α)` is a prime power and `α c₀ (q + 1)` is an integer,
then there is an infinite family of `(c₀ (q + 1), α c₀ (q + 1))`-biregular
unique neighbour expanders.

Encoding notes.  `q̂` is curried as `qhat : ℕ → ℝ → ℕ`, and "`q` is a prime
power" is `IsPrimePow q`.  "`α c₀ (q + 1)` is an integer" is encoded by
quantifying over a natural number `d` with `(d : ℝ) = α * (c₀ * (q + 1))`;
the number is positive, so nothing is lost by taking `d` in `ℕ`.  The family
is a sequence `G n` of bipartite multigraphs (Section 3.1 allows parallel
edges, and the gadget of Lemma 11 may have them), `(c, d)`-biregular counting
parallel edges, with `|L_n| + |R_n| → ∞`; "unique neighbour expander family"
is `IsUniqueNeighbourExpanderFamily` (Section 1).  The clause
"polynomial-time construction" is a statement about a model of computation
and is not asserted; only the existence of the family is.

This is the target statement of problem P071; its `sorry` is the only one in
the file. -/
theorem P071 :
    ∃ qhat : ℕ → ℝ → ℕ, ∀ c₀ : ℕ, 5 < c₀ → ∀ α : ℝ, 1 < α →
      ∀ q : ℕ, IsPrimePow q → qhat c₀ α < q →
        ∀ d : ℕ, (d : ℝ) = α * ((c₀ : ℝ) * ((q : ℝ) + 1)) →
          ∃ G : ℕ → BipartiteMultigraph,
            IsUniqueNeighbourExpanderFamily G (c₀ * (q + 1)) d := by
  sorry
