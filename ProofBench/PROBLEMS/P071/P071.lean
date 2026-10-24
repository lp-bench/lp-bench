import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace RamanujanRoutedProduct

open Finset

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- `N(S)`: the neighbourhood of a set `S` of left vertices. A bipartite graph is
given, as in Asherov–Dinur, by the function `nbr` sending a left vertex to its set of
right neighbours. -/
def nbhd (nbr : L → Finset R) (S : Finset L) : Finset R :=
  S.biUnion nbr

/-- The fibre of a right vertex `v` over `S`: the vertices of `S` adjacent to `v`.
Its size is the degree of `v` in the subgraph induced by `S` and `N(S)`. -/
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

/-- The unique-neighbour property up to size `t`: every nonempty set of at most `t`
left vertices has a unique neighbour (the property of the gadget in Lemma 11). -/
def HasUniqueNeighbourProperty (nbr : L → Finset R) (t : ℕ) : Prop :=
  ∀ S : Finset L, S.Nonempty → S.card ≤ t → ∃ v : R, IsUniqueNeighbour nbr S v

omit [DecidableEq L] in
/-- Double counting: the left degrees over `S` and the induced right degrees over
any `N ⊇ N(S)` have the same sum. -/
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

omit [DecidableEq L] in
/-- If every vertex of `S` has degree `c` and `|N(S)| > c|S|/2`, then `S` has a
unique neighbour (Section 2 of Asherov–Dinur). -/
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

variable {R₀ : Type*} [DecidableEq R₀] [Fintype R₀]

/-- The set `S'` of Lemma 12: the indices `i` for which the `i`-th neighbour
`Ed v i` of the right vertex `v` lies in `S`. -/
def gadgetTrace {d : ℕ} (Ed : R → Fin d → L) (S : Finset L) (v : R) : Finset (Fin d) :=
  Finset.univ.filter fun i => Ed v i ∈ S

/-- The routed product of Section 6.1, with left side `L` and right side `R × R₀`.
The big graph is given by `Ed v i`, the `i`-th neighbour of the right vertex `v`, and
the gadget by `gnbr` on the left side `Fin d`; `x` is joined to `(v, j)` when
`x = Ed v i` for some `i` adjacent to `j` in the gadget. -/
def routedProduct {d : ℕ} [Fintype R] (Ed : R → Fin d → L)
    (gnbr : Fin d → Finset R₀) (x : L) : Finset (R × R₀) :=
  Finset.univ.filter fun p => ∃ i : Fin d, Ed p.1 i = x ∧ p.2 ∈ gnbr i

omit [DecidableEq R] in
/-- Membership in a neighbourhood of the routed product. -/
@[simp]
theorem mem_routedProduct {d : ℕ} [Fintype R] (Ed : R → Fin d → L)
    (gnbr : Fin d → Finset R₀) (x : L) (p : R × R₀) :
    p ∈ routedProduct Ed gnbr x ↔ ∃ i : Fin d, Ed p.1 i = x ∧ p.2 ∈ gnbr i := by
  classical
  simp [routedProduct]

/-- Lemma 12 of Asherov–Dinur: if `j` is a unique neighbour of `S' = gadgetTrace Ed S v`
in the gadget, then `(v, j)` is a unique neighbour of `S` in the routed product. -/
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

/-- If the gadget has the unique-neighbour property up to size `t` and `S` has a
nonempty trace of size at most `t` at some right vertex `v`, then `S` has a unique
neighbour in the routed product. -/
theorem exists_uniqueNeighbour_routedProduct {d t : ℕ} [Fintype R]
    (Ed : R → Fin d → L) (gnbr : Fin d → Finset R₀)
    (hgadget : HasUniqueNeighbourProperty gnbr t) (S : Finset L) (v : R)
    (hne : (gadgetTrace Ed S v).Nonempty) (hsmall : (gadgetTrace Ed S v).card ≤ t) :
    ∃ w : R × R₀, IsUniqueNeighbour (routedProduct Ed gnbr) S w := by
  obtain ⟨j, hj⟩ := hgadget (gadgetTrace Ed S v) hne hsmall
  exact ⟨(v, j), card_filter_routedProduct_eq_one Ed gnbr S v j hj⟩

/-- A finite bipartite multigraph with left side `Fin nL`, right side `Fin nR` and
`mult u v` parallel edges between `u` and `v`; parallel edges are allowed, as in
Section 3.1 of Asherov–Dinur. -/
structure BipartiteMultigraph where
  /-- The number of left vertices `|L|`. -/
  nL : ℕ
  /-- The number of right vertices `|R|`. -/
  nR : ℕ
  /-- The number of edges between a left vertex and a right vertex. -/
  mult : Fin nL → Fin nR → ℕ

namespace BipartiteMultigraph

/-- The neighbourhood function of the left side: `v ∈ nbr u` when there is at least
one edge between `u` and `v`. Neighbourhoods and unique neighbours ignore
multiplicities; degrees count them. -/
def nbr (G : BipartiteMultigraph) (u : Fin G.nL) : Finset (Fin G.nR) :=
  Finset.univ.filter fun v => 0 < G.mult u v

/-- Membership in `nbr u`, unfolded. -/
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

/-- A unique-neighbour expander family (Section 1): `(c, d)`-biregular multigraphs
`G n` with `|L_n| + |R_n| → ∞` and some `δ > 0` such that every nonempty `S ⊆ L_n`
with `|S| ≤ δ |L_n|` has a unique neighbour (the empty set has none). -/
def IsUniqueNeighbourExpanderFamily (G : ℕ → BipartiteMultigraph) (c d : ℕ) : Prop :=
  (∀ n, (G n).IsBiregular c d) ∧
    Filter.Tendsto (fun n => (G n).nL + (G n).nR) Filter.atTop Filter.atTop ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ S : Finset (Fin (G n).nL), S.Nonempty →
      (S.card : ℝ) ≤ δ * ((G n).nL : ℝ) → ∃ v, IsUniqueNeighbour (G n).nbr S v

end RamanujanRoutedProduct

open RamanujanRoutedProduct in
/-- Theorem 1 of Asherov–Dinur (arXiv:2301.03072), existence form: there is `q̂` such
that for all `c₀ > 5`, `α > 1` and prime powers `q > q̂(c₀, α)` with `d = α c₀ (q + 1)`
an integer, there is a `(c₀ (q + 1), d)`-biregular unique-neighbour expander family.
The paper's polynomial-time construction clause is not formalised. -/
theorem P071 :
    ∃ qhat : ℕ → ℝ → ℕ, ∀ c₀ : ℕ, 5 < c₀ → ∀ α : ℝ, 1 < α →
      ∀ q : ℕ, IsPrimePow q → qhat c₀ α < q →
        ∀ d : ℕ, (d : ℝ) = α * ((c₀ : ℝ) * ((q : ℝ) + 1)) →
          ∃ G : ℕ → BipartiteMultigraph,
            IsUniqueNeighbourExpanderFamily G (c₀ * (q + 1)) d := by
  sorry
