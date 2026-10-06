import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# P096: characteristic and matching polynomials of a uniform hypertree

This file formalizes part of

  H. Li, L. Su and S. Fallat, *On a relationship between the characteristic and
  matching polynomials of a uniform hypertree*, arXiv:2306.16247.

The paper's dependency graph for Theorem 4.10 is:

* Section 2.1: resultants and the characteristic polynomial `phi_A` of a tensor;
* Section 2.2: `r`-uniform hypergraphs, hypertrees, subgraphs, the boundary
  `bd(H)` of a subgraph, and **Lemma 2.4**, `m = (n-1)/(r-1)` for an `r`-tree;
* Section 3: the generalized incidence matrix, toppling, recurrent
  configurations and the toppled digraph (Lemmas 3.5, Proposition 3.7);
* Section 4: Lemmas 4.1-4.7 on toppling sequences of an `r`-tree with a good
  ordering, culminating in Theorem 4.9, `prod phi_H ^ a_H` divides `phi_T`, and
  Theorem 4.10, the equality
  `phi_T = prod over connected H of phi_H ^ a_H` with
  `a_H = b^(m - e(H) - |bd(H)|) * c^e(H) * (b - c)^|bd(H)|`,
  `b = (r-1)^(r-1)`, `c = r^(r-2)`;
* the classical Theorem 1.1, `phi_T = phi_T` for ordinary trees, recovered from
  Theorem 4.10 at `r = 2`.

The target of the problem is the paper's main theorem, **Theorem 4.10**,
stated at the end of this file as `P096` and proved
by `sorry` -- the single `sorry` of the file.  The characteristic polynomial
`phi_T` of the adjacency tensor is defined concretely, with no placeholder,
through the Macaulay determinant formula of Proposition 2.3
(Cox--Little--O'Shea): for the eigenvalue system
`lambda x_i^(r-1) = sum over e in E_i of x_(e \ {i})`, the Macaulay matrix in
the monomials of total degree `d = n(r-2) + 1` is exactly `lambda I - C` for
the 0/1 transfer matrix `C` of the toppled digraph of Section 3, so
`charPoly` below is the polynomial quotient of these two explicit matrix
characteristic polynomials. Identifying it with the tensor resultant requires
the exact-division theorem of Proposition 2.3; that bridge is not yet proved
here. `P096_Macaulay.lean` verifies exactness and agreement with the ordinary
adjacency characteristic polynomial for `r = 2` independently of P096.

Everything else below is proved from first principles with no `sorry` and no
new axioms.  The results formalized in full are

* `IsRTree`, the inductive description of an `r`-tree as a coalescence of
  edges, `isUniform_of_isRTree`, and `card_vertices_of_isRTree`, which is
  **Lemma 2.4**;
* `matchingPoly`, the matching polynomial of an `r`-uniform hypergraph, with
  `matchingCount_zero` and `matchingPoly_single_edge`;
* `aExp`, the exponent `a_H` of Theorem 4.10, and `aExp_two`, its computation
  at `r = 2`, where `b - c = 0`;
* `boundary_self`, that `T` has empty boundary in itself, and
  `prod_matchingPoly_two`, the statement that at `r = 2` the product of
  Theorem 4.10 collapses to the single factor `phi_T`, which is exactly the
  classical Theorem 1.1.

The new definitions supporting the target statement are `HAdj`, `IsConnected`
and `connectedSubgraphs` (Section 2.2), `degree`, and the characteristic
polynomial chain `macaulayDegree`, `degreeMonomials`, `monClass`,
`ToppleStep`, `IsReducedMon`, `toppleMatrix`, `toppleMatrixNonReduced` and
`charPoly` (Sections 2.1 and 3).  `prod_matchingPoly_two` formalizes the
reduction of Theorem 4.10 to Theorem 1.1 that the paper records at the end of
Section 4.

Vertices are natural numbers and a hypergraph is presented by its edge set, a
finite family of finite vertex sets, exactly as in Section 2.2.
-/

namespace UniformHypertree

open Finset

/-- A hypergraph, presented by its edge set. -/
abbrev EdgeSet := Finset (Finset ℕ)

/-- The vertex set of a hypergraph: the union of its edges. -/
def vertices (E : EdgeSet) : Finset ℕ :=
  E.biUnion id

@[simp]
theorem mem_vertices {E : EdgeSet} {v : ℕ} : v ∈ vertices E ↔ ∃ e ∈ E, v ∈ e := by
  simp [vertices]

theorem mem_vertices_of_mem {E : EdgeSet} {e : Finset ℕ} {v : ℕ} (he : e ∈ E)
    (hv : v ∈ e) : v ∈ vertices E :=
  mem_vertices.mpr ⟨e, he, hv⟩

@[simp]
theorem vertices_singleton (e : Finset ℕ) : vertices {e} = e := by
  ext v; simp

theorem vertices_insert (e : Finset ℕ) (E : EdgeSet) :
    vertices (insert e E) = e ∪ vertices E := by
  ext v
  simp only [mem_vertices, Finset.mem_union, Finset.mem_insert]
  constructor
  · rintro ⟨f, hf | hf, hvf⟩
    · exact Or.inl (hf ▸ hvf)
    · exact Or.inr ⟨f, hf, hvf⟩
  · rintro (hv | ⟨f, hf, hvf⟩)
    · exact ⟨e, Or.inl rfl, hv⟩
    · exact ⟨f, Or.inr hf, hvf⟩

/-- `H` is `r`-uniform when every edge has exactly `r` vertices. -/
def IsUniform (r : ℕ) (E : EdgeSet) : Prop :=
  ∀ e ∈ E, e.card = r

/-- The *boundary* `bd(H)` of a subgraph `H` of `T` (Section 2.2): the edges of
`T` meeting both `V(H)` and its complement in `V(T)`. -/
def boundary (E F : EdgeSet) : EdgeSet :=
  E.filter fun e => (∃ v ∈ e, v ∈ vertices F) ∧ (∃ w ∈ e, w ∉ vertices F)

/-- A hypergraph has empty boundary in itself: every edge of `T` lies inside
`V(T)`.  This is the `H = T` case of the `r = 2` computation at the end of
Section 4. -/
theorem boundary_self (E : EdgeSet) : boundary E E = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [boundary, Finset.mem_filter] at he
  obtain ⟨heE, -, w, hwe, hwV⟩ := he
  exact hwV (mem_vertices_of_mem heE hwe)

/-! ## `r`-trees

An `r`-tree is a connected `r`-uniform hypergraph without cycles.  Equivalently
(Section 4, "coalescence"), it is built from a single edge by repeatedly gluing
a new `r`-edge to an already-present vertex, all of whose other `r-1` vertices
are new.  This is the description formalized here. -/

/-- The inductive description of an `r`-tree by coalescence of edges. -/
inductive IsRTree (r : ℕ) : EdgeSet → Prop
  | single (e : Finset ℕ) (he : e.card = r) : IsRTree r {e}
  | cons {E : EdgeSet} {e : Finset ℕ} {v : ℕ} (h : IsRTree r E) (he : e.card = r)
      (hv : v ∈ vertices E) (hve : v ∈ e)
      (hfresh : ∀ w ∈ e, w ≠ v → w ∉ vertices E) : IsRTree r (insert e E)

/-- An `r`-tree is `r`-uniform. -/
theorem isUniform_of_isRTree {r : ℕ} {E : EdgeSet} (h : IsRTree r E) :
    IsUniform r E := by
  induction h with
  | single e he =>
      intro f hf
      rw [Finset.mem_singleton] at hf
      subst hf
      exact he
  | cons _ he _ _ _ ih =>
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf'
      · exact he
      · exact ih f hf'

/-- In the coalescence step the new edge is genuinely new, because it carries a
fresh vertex.  This needs `2 <= r`, so that the new edge has a vertex other than
the gluing vertex. -/
theorem notMem_of_cons {r : ℕ} {E : EdgeSet} {e : Finset ℕ} {v : ℕ} (hr : 2 ≤ r)
    (he : e.card = r) (hve : v ∈ e) (hfresh : ∀ w ∈ e, w ≠ v → w ∉ vertices E) :
    e ∉ E := by
  intro hmem
  have hcard : 1 < (e.erase v).card + 1 := by
    rw [Finset.card_erase_add_one hve, he]; omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (e.erase v).card)
  have hwv : w ≠ v := Finset.ne_of_mem_erase hw
  have hwe : w ∈ e := Finset.mem_of_mem_erase hw
  exact hfresh w hwe hwv (mem_vertices_of_mem hmem hwe)

/-- **Lemma 2.4.**  An `r`-tree with `m` edges has `m (r-1) + 1` vertices, that
is `m = (n-1)/(r-1)`. -/
theorem card_vertices_of_isRTree {r : ℕ} (hr : 2 ≤ r) {E : EdgeSet}
    (h : IsRTree r E) : (vertices E).card = E.card * (r - 1) + 1 := by
  induction h with
  | single e he =>
      rw [vertices_singleton, he, Finset.card_singleton]
      omega
  | @cons E e v h he hv hve hfresh ih =>
      have hnew : e ∉ E := notMem_of_cons hr he hve hfresh
      have hsdiff : e \ vertices E = e.erase v := by
        ext w
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨hwe, hwV⟩
          refine ⟨?_, hwe⟩
          rintro rfl
          exact hwV hv
        · rintro ⟨hwv, hwe⟩
          exact ⟨hwe, hfresh w hwe hwv⟩
      have hunion : vertices (insert e E) = (e \ vertices E) ∪ vertices E := by
        rw [vertices_insert, Finset.sdiff_union_self_eq_union]
      have hcard : (vertices (insert e E)).card = (r - 1) + (vertices E).card := by
        rw [hunion, Finset.card_union_of_disjoint Finset.sdiff_disjoint, hsdiff,
          Finset.card_erase_of_mem hve, he]
      rw [hcard, ih, Finset.card_insert_of_notMem hnew]
      ring

/-! ## The matching polynomial of an `r`-uniform hypergraph

`phi_H(lambda) = sum over k of (-1)^k m_H(k) lambda^(n - r k)`, where `m_H(k)`
is the number of `k`-matchings of `H` and `n = |V(H)|`.  For `r = 2` this is
the usual matching polynomial of a graph, and for the `3`-tree of Example 4.11
it returns the values listed in Table 1. -/

/-- A family of edges is a matching when its members are pairwise disjoint. -/
def IsMatching (F : EdgeSet) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, e ≠ f → e ∩ f = ∅

instance : DecidablePred IsMatching := fun F => by
  unfold IsMatching; infer_instance

/-- `m_H(k)`, the number of `k`-matchings of `H`. -/
def matchingCount (E : EdgeSet) (k : ℕ) : ℕ :=
  ((E.powersetCard k).filter IsMatching).card

@[simp]
theorem matchingCount_zero (E : EdgeSet) : matchingCount E 0 = 1 := by
  have hempty : IsMatching (∅ : EdgeSet) := by
    intro e he
    exact absurd he (Finset.notMem_empty e)
  rw [matchingCount, Finset.powersetCard_zero, Finset.filter_singleton, if_pos hempty,
    Finset.card_singleton]

/-- The matching polynomial `phi_H` of an `r`-uniform hypergraph `H`. -/
noncomputable def matchingPoly (r : ℕ) (E : EdgeSet) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (E.card + 1),
    Polynomial.C ((-1) ^ k * (matchingCount E k : ℤ))
      * Polynomial.X ^ ((vertices E).card - r * k)

/-- The matching polynomial of a single `r`-edge is `lambda^r - 1`, matching the
entries `lambda^3 - 1` of Table 1 for the `3`-uniform example. -/
theorem matchingPoly_single_edge {r : ℕ} {e : Finset ℕ} (he : e.card = r) :
    matchingPoly r {e} = Polynomial.X ^ r - 1 := by
  have hcount : matchingCount {e} 1 = 1 := by
    have hsub : ({e} : EdgeSet).powersetCard 1 = {({e} : EdgeSet)} := by
      have h1 : ({e} : EdgeSet).card = 1 := Finset.card_singleton e
      rw [← h1, Finset.powersetCard_self]
    have hm : IsMatching ({e} : EdgeSet) := by
      intro a ha b hb hab
      rw [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab
    rw [matchingCount, hsub, Finset.filter_singleton, if_pos hm, Finset.card_singleton]
  rw [matchingPoly, Finset.card_singleton, vertices_singleton, he]
  rw [Finset.sum_range_succ, Finset.sum_range_one, hcount]
  simp [sub_eq_add_neg]

/-! ## The exponent `a_H` and the case `r = 2` -/

/-- `b = (r-1)^(r-1)` from Theorem 4.9. -/
def bCoeff (r : ℕ) : ℕ := (r - 1) ^ (r - 1)

/-- `c = r^(r-2)` from Theorem 4.9. -/
def cCoeff (r : ℕ) : ℕ := r ^ (r - 2)

/-- The exponent `a_H = b^(m - e(H) - |bd(H)|) c^e(H) (b - c)^|bd(H)|` of
Theorem 4.10, as a function of the size `m` of `T`, the size `e(H)` of `H` and
the size of the boundary of `H`. -/
def aExp (r m eH bH : ℕ) : ℕ :=
  bCoeff r ^ (m - eH - bH) * cCoeff r ^ eH * (bCoeff r - cCoeff r) ^ bH

@[simp]
theorem bCoeff_two : bCoeff 2 = 1 := by decide

@[simp]
theorem cCoeff_two : cCoeff 2 = 1 := by decide

/-- **The `r = 2` computation at the end of Section 4.**  Since
`b - c = (r-1)^(r-1) - r^(r-2)` vanishes at `r = 2`, the exponent `a_H` is `1`
for a subgraph with empty boundary and `0` for every other subgraph. -/
theorem aExp_two (m eH bH : ℕ) : aExp 2 m eH bH = if bH = 0 then 1 else 0 := by
  rw [aExp, bCoeff_two, cCoeff_two, one_pow, one_pow, one_mul, one_mul]
  cases bH with
  | zero => simp
  | succ n => simp

theorem aExp_two_of_boundary_empty (m eH : ℕ) : aExp 2 m eH 0 = 1 := by
  rw [aExp_two]; simp

theorem aExp_two_of_boundary_nonempty {m eH bH : ℕ} (h : bH ≠ 0) :
    aExp 2 m eH bH = 0 := by
  rw [aExp_two, if_neg h]

/-- **Theorem 4.10 at `r = 2` is the classical Theorem 1.1.**  Let `T` be a
`2`-tree and let `S` be any family of subgraphs of `T` containing `T` itself, in
which every member other than `T` has a nonempty boundary — as every proper
connected subgraph of a tree does.  Then the product of Theorem 4.10 collapses to
the single factor `phi_T`, so the theorem reduces to
`phi_T(lambda) = phi_T(lambda)`. -/
theorem prod_matchingPoly_two (E : EdgeSet) (S : Finset EdgeSet) (hE : E ∈ S)
    (hproper : ∀ F ∈ S, F ≠ E → (boundary E F).Nonempty) :
    (∏ F ∈ S, (matchingPoly 2 F) ^ aExp 2 E.card F.card (boundary E F).card)
      = matchingPoly 2 E := by
  refine (Finset.prod_eq_single E ?_ ?_).trans ?_
  · intro F hF hFE
    have hpos : 0 < (boundary E F).card := Finset.card_pos.mpr (hproper F hF hFE)
    have hne : (boundary E F).card ≠ 0 := by omega
    rw [aExp_two_of_boundary_nonempty hne, pow_zero]
  · intro hcon
    exact absurd hE hcon
  · rw [boundary_self, Finset.card_empty, aExp_two_of_boundary_empty, pow_one]

/-! ## Connectivity and the connected subgraphs -/

/-- Two vertices are adjacent when some edge contains both (Section 2.2). -/
def HAdj (E : EdgeSet) (u v : ℕ) : Prop :=
  ∃ e ∈ E, u ∈ e ∧ v ∈ e

/-- A hypergraph is connected when any two of its vertices are joined by a
path (Section 2.2). -/
def IsConnected (E : EdgeSet) : Prop :=
  ∀ u ∈ vertices E, ∀ v ∈ vertices E, Relation.ReflTransGen (HAdj E) u v

open scoped Classical in
/-- The connected subgraphs of `T` containing at least one edge, presented by
their edge sets: `H = (V(F), F)` for a nonempty connected `F ⊆ E(T)`.
Together with the single-vertex subgraphs `({v}, ∅)` for `v ∈ V(T)`, these
are exactly the connected subgraphs `H ⊑ T` over which Theorem 4.10 takes its
product. -/
noncomputable def connectedSubgraphs (E : EdgeSet) : Finset EdgeSet :=
  E.powerset.filter fun F => F.Nonempty ∧ IsConnected F

theorem mem_connectedSubgraphs {E F : EdgeSet} :
    F ∈ connectedSubgraphs E ↔ F ⊆ E ∧ F.Nonempty ∧ IsConnected F := by
  classical
  simp [connectedSubgraphs, Finset.mem_filter, Finset.mem_powerset]

/-- The degree of a vertex: the number of edges containing it.  For the
single-vertex subgraph `({v}, ∅)` the boundary is the star `E_v`, of size
`deg(v)`. -/
def degree (E : EdgeSet) (v : ℕ) : ℕ :=
  (E.filter fun e => v ∈ e).card

/-! ## The characteristic polynomial of the adjacency tensor

Section 2.2 defines `phi_T` as the resultant `Res(F_1, ..., F_n)` of the
eigenvalue system `F_i = lambda x_i^(r-1) - sum over e in E_i of x_(e\{i})`.
We realize it through the Macaulay determinant formula of Proposition 2.3:
`Res = D_n / D'_n`, where `D_n` is the determinant of the Macaulay matrix of
the system in the monomials of total degree `d = n(r-2) + 1`, and `D'_n` the
determinant of its submatrix on the non-reduced monomials.  Multiplying the
equation of the class vertex `i` of a monomial `alpha` by
`x^alpha / x_i^(r-1)` shows that the Macaulay matrix is `lambda I - C`, where
`C` is the 0/1 transfer matrix sending `alpha` to
`alpha - (r-1) 1_i + 1_(e \ {i})` for each edge `e` at `i` -- the toppled
digraph of Section 3.  Hence `D_n` and `D'_n` are characteristic polynomials
of explicit integer matrices; both are monic, so `D'_n ≠ 0` holds
automatically. Monicity alone does not imply exact division. The general
resultant identity and zero-remainder assertion remain to be formalized. -/

/-- The Macaulay degree `d = n(r-2) + 1` of the eigenvalue system, where `n`
is the number of vertices (Section 2.1, with `n` polynomials of degree
`r - 1`). -/
def macaulayDegree (r : ℕ) (E : EdgeSet) : ℕ :=
  (vertices E).card * (r - 2) + 1

/-- The monomials `x^alpha` of total degree `d` in the vertex variables,
recorded by their exponent vectors. -/
def degreeMonomials (r : ℕ) (E : EdgeSet) : Finset (ℕ →₀ ℕ) :=
  Finset.finsuppAntidiag (vertices E) (macaulayDegree r E)

/-- The class of a monomial, following the partition (2) of Section 2.1: the
least vertex `i` with `alpha_i >= r - 1`.  By pigeonhole every monomial of
degree `n(r-2) + 1` has such a vertex when `r >= 2`, so the default value `0`
is never taken on genuine inputs. -/
def monClass (r : ℕ) (E : EdgeSet) (α : ℕ →₀ ℕ) : ℕ :=
  WithBot.unbotD 0 (((vertices E).filter fun i => r - 1 ≤ α i).min)

/-- The toppling relation of Section 3: `beta` is obtained from `alpha` by
toppling at the vertex `i` along the edge `e`, that is,
`beta = alpha - (r-1) 1_i + 1_(e \ {i})`, written additively so that no
truncated subtraction is involved. -/
def ToppleStep (r : ℕ) (i : ℕ) (e : Finset ℕ) (α β : ℕ →₀ ℕ) : Prop :=
  β + Finsupp.single i (r - 1) = α + ∑ j ∈ e.erase i, Finsupp.single j 1

/-- A monomial of degree `d` is *reduced* (Section 2.1) when exactly one
vertex `i` has `alpha_i >= r - 1`. -/
def IsReducedMon (r : ℕ) (E : EdgeSet) (α : ℕ →₀ ℕ) : Prop :=
  ((vertices E).filter fun i => r - 1 ≤ α i).card = 1

open scoped Classical in
/-- The transfer matrix `C` of the toppled digraph on the degree-`d`
monomials: the entry at `(alpha, beta)` counts the edges `e` at the class
vertex of `alpha` that topple `alpha` to `beta`.  The Macaulay matrix of the
eigenvalue system is `lambda I - C`, so `D_n = det(lambda I - C)` is the
characteristic polynomial of `C`. -/
noncomputable def toppleMatrix (r : ℕ) (E : EdgeSet) :
    Matrix ↥(degreeMonomials r E) ↥(degreeMonomials r E) ℤ :=
  Matrix.of fun a b =>
    ((E.filter fun e =>
      monClass r E a.1 ∈ e ∧ ToppleStep r (monClass r E a.1) e a.1 b.1).card : ℤ)

open scoped Classical in
/-- The non-reduced monomials of degree `d`. -/
noncomputable def nonReducedMonomials (r : ℕ) (E : EdgeSet) : Finset (ℕ →₀ ℕ) :=
  (degreeMonomials r E).filter fun α => ¬ IsReducedMon r E α

open scoped Classical in
/-- The restriction `C'` of the transfer matrix to the non-reduced monomials;
`D'_n = det(lambda I - C')` is the extraneous-factor determinant of
Proposition 2.3. -/
noncomputable def toppleMatrixNonReduced (r : ℕ) (E : EdgeSet) :
    Matrix ↥(nonReducedMonomials r E) ↥(nonReducedMonomials r E) ℤ :=
  Matrix.of fun a b =>
    ((E.filter fun e =>
      monClass r E a.1 ∈ e ∧ ToppleStep r (monClass r E a.1) e a.1 b.1).card : ℤ)

/-- The polynomial quotient in the Macaulay formula `Res = D_n / D'_n`
(Proposition 2.3). The denominator is monic and nonzero. Agreement with the
tensor characteristic polynomial requires a separate resultant identity;
it does not follow merely from using polynomial division. -/
noncomputable def charPoly (r : ℕ) (E : EdgeSet) : Polynomial ℤ := by
  classical
  exact (toppleMatrix r E).charpoly.divByMonic (toppleMatrixNonReduced r E).charpoly

/-! ## Theorem 4.10: the main theorem -/

end UniformHypertree

open UniformHypertree in
/-- **Theorem 4.10**, the main theorem of the paper.  For an `r`-tree `T` of
size `m` with `r >= 2`,

`phi_T(lambda) = prod over connected subgraphs H of T of phi_H(lambda)^(a_H)`

with `a_H = b^(m - e(H) - |bd(H)|) c^(e(H)) (b - c)^(|bd(H)|)`,
`b = (r-1)^(r-1)` and `c = r^(r-2)`.  The connected subgraphs of `T` are the
single vertices `({v}, ∅)` -- with matching polynomial `lambda`, size
`e(H) = 0` and boundary the star of `v`, of size `deg(v)` -- together with
the subgraphs `(V(F), F)` for the nonempty connected edge subsets `F` of
`E(T)`; the product below is split accordingly.

This is the target statement of problem P096; its `sorry` is the only one in
the file. -/
theorem P096 {r : ℕ} (hr : 2 ≤ r) {E : EdgeSet}
    (hT : IsRTree r E) :
    charPoly r E
      = (∏ v ∈ vertices E,
          (Polynomial.X : Polynomial ℤ) ^ aExp r E.card 0 (degree E v))
        * ∏ F ∈ connectedSubgraphs E,
            matchingPoly r F ^ aExp r E.card F.card (boundary E F).card := by
  sorry
