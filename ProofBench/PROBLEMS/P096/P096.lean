import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

namespace UniformHypertree

open Finset

/-- A hypergraph, presented by its edge set. -/
abbrev EdgeSet := Finset (Finset ℕ)

/-- The vertex set of a hypergraph: the union of its edges. -/
def vertices (E : EdgeSet) : Finset ℕ :=
  E.biUnion id

/-- Membership in the vertex set. -/
@[simp]
theorem mem_vertices {E : EdgeSet} {v : ℕ} : v ∈ vertices E ↔ ∃ e ∈ E, v ∈ e := by
  simp [vertices]

/-- A vertex of an edge is a vertex of the hypergraph. -/
theorem mem_vertices_of_mem {E : EdgeSet} {e : Finset ℕ} {v : ℕ} (he : e ∈ E)
    (hv : v ∈ e) : v ∈ vertices E :=
  mem_vertices.mpr ⟨e, he, hv⟩

/-- The vertex set of a single edge is that edge. -/
@[simp]
theorem vertices_singleton (e : Finset ℕ) : vertices {e} = e := by
  ext v; simp

/-- The vertex set after adding an edge. -/
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

/-- A hypergraph has empty boundary in itself. -/
theorem boundary_self (E : EdgeSet) : boundary E E = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [boundary, Finset.mem_filter] at he
  obtain ⟨heE, -, w, hwe, hwV⟩ := he
  exact hwV (mem_vertices_of_mem heE hwe)

/-- An `r`-tree, described by coalescence (Section 4): starting from one `r`-edge,
repeatedly glue a new `r`-edge at one existing vertex, its other `r - 1` vertices
being new. -/
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

/-- For `2 ≤ r`, the edge added in a coalescence step is not already present. -/
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

/-- Lemma 2.4: an `r`-tree with `m` edges has `m (r-1) + 1` vertices. -/
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

/-- A family of edges is a matching when its members are pairwise disjoint. -/
def IsMatching (F : EdgeSet) : Prop :=
  ∀ e ∈ F, ∀ f ∈ F, e ≠ f → e ∩ f = ∅

instance : DecidablePred IsMatching := fun F => by
  unfold IsMatching; infer_instance

/-- `m_H(k)`, the number of `k`-matchings of `H`. -/
def matchingCount (E : EdgeSet) (k : ℕ) : ℕ :=
  ((E.powersetCard k).filter IsMatching).card

/-- There is exactly one `0`-matching. -/
@[simp]
theorem matchingCount_zero (E : EdgeSet) : matchingCount E 0 = 1 := by
  have hempty : IsMatching (∅ : EdgeSet) := by
    intro e he
    exact absurd he (Finset.notMem_empty e)
  rw [matchingCount, Finset.powersetCard_zero, Finset.filter_singleton, if_pos hempty,
    Finset.card_singleton]

/-- The matching polynomial `phi_H(λ) = ∑_k (-1)^k m_H(k) λ^(n - r k)` of an
`r`-uniform hypergraph `H` with `n` vertices. -/
noncomputable def matchingPoly (r : ℕ) (E : EdgeSet) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (E.card + 1),
    Polynomial.C ((-1) ^ k * (matchingCount E k : ℤ))
      * Polynomial.X ^ ((vertices E).card - r * k)

/-- The matching polynomial of a single `r`-edge is `λ^r - 1`. -/
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

/-- `b = (r-1)^(r-1)` from Theorem 4.9. -/
def bCoeff (r : ℕ) : ℕ := (r - 1) ^ (r - 1)

/-- `c = r^(r-2)` from Theorem 4.9. -/
def cCoeff (r : ℕ) : ℕ := r ^ (r - 2)

/-- The exponent `a_H = b^(m - e(H) - |bd(H)|) c^e(H) (b - c)^|bd(H)|` of
Theorem 4.10, as a function of the size `m` of `T`, the size `e(H)` of `H` and
the size of the boundary of `H`. -/
def aExp (r m eH bH : ℕ) : ℕ :=
  bCoeff r ^ (m - eH - bH) * cCoeff r ^ eH * (bCoeff r - cCoeff r) ^ bH

/-- `b = 1` for `r = 2`. -/
@[simp]
theorem bCoeff_two : bCoeff 2 = 1 := by decide

/-- `c = 1` for `r = 2`. -/
@[simp]
theorem cCoeff_two : cCoeff 2 = 1 := by decide

/-- For `r = 2`, where `b - c = 0`, the exponent `a_H` is `1` for a subgraph with
empty boundary and `0` otherwise. -/
theorem aExp_two (m eH bH : ℕ) : aExp 2 m eH bH = if bH = 0 then 1 else 0 := by
  rw [aExp, bCoeff_two, cCoeff_two, one_pow, one_pow, one_mul, one_mul]
  cases bH with
  | zero => simp
  | succ n => simp

/-- For `r = 2`, `a_H = 1` when the boundary is empty. -/
theorem aExp_two_of_boundary_empty (m eH : ℕ) : aExp 2 m eH 0 = 1 := by
  rw [aExp_two]; simp

/-- For `r = 2`, `a_H = 0` when the boundary is nonempty. -/
theorem aExp_two_of_boundary_nonempty {m eH bH : ℕ} (h : bH ≠ 0) :
    aExp 2 m eH bH = 0 := by
  rw [aExp_two, if_neg h]

/-- For `r = 2`, if `S` contains `T` and every other member of `S` has nonempty
boundary in `T`, the product of Theorem 4.10 over `S` is the single factor `phi_T`. -/
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

/-- Two vertices are adjacent when some edge contains both (Section 2.2). -/
def HAdj (E : EdgeSet) (u v : ℕ) : Prop :=
  ∃ e ∈ E, u ∈ e ∧ v ∈ e

/-- A hypergraph is connected when any two of its vertices are joined by a
path (Section 2.2). -/
def IsConnected (E : EdgeSet) : Prop :=
  ∀ u ∈ vertices E, ∀ v ∈ vertices E, Relation.ReflTransGen (HAdj E) u v

open scoped Classical in
/-- The connected subgraphs of `T` with at least one edge, given by their edge
sets `F`: the nonempty connected `F ⊆ E(T)`, with `H = (V(F), F)`. -/
noncomputable def connectedSubgraphs (E : EdgeSet) : Finset EdgeSet :=
  E.powerset.filter fun F => F.Nonempty ∧ IsConnected F

/-- Membership in `connectedSubgraphs`. -/
theorem mem_connectedSubgraphs {E F : EdgeSet} :
    F ∈ connectedSubgraphs E ↔ F ⊆ E ∧ F.Nonempty ∧ IsConnected F := by
  classical
  simp [connectedSubgraphs, Finset.mem_filter, Finset.mem_powerset]

/-- The degree of a vertex: the number of edges containing it. -/
def degree (E : EdgeSet) (v : ℕ) : ℕ :=
  (E.filter fun e => v ∈ e).card

/-- The Macaulay degree `d = n(r-2) + 1` of the eigenvalue system, where `n` is
the number of vertices. -/
def macaulayDegree (r : ℕ) (E : EdgeSet) : ℕ :=
  (vertices E).card * (r - 2) + 1

/-- The monomials `x^α` of total degree `d` in the vertex variables,
recorded by their exponent vectors. -/
def degreeMonomials (r : ℕ) (E : EdgeSet) : Finset (ℕ →₀ ℕ) :=
  Finset.finsuppAntidiag (vertices E) (macaulayDegree r E)

/-- The class of a monomial `x^α` (Section 2.1): the least vertex `i` with
`α_i ≥ r - 1`.  For `r ≥ 2` every monomial of degree `n(r-2) + 1` has such a vertex,
so the default value `0` is never used. -/
def monClass (r : ℕ) (E : EdgeSet) (α : ℕ →₀ ℕ) : ℕ :=
  WithBot.unbotD 0 (((vertices E).filter fun i => r - 1 ≤ α i).min)

/-- Toppling (Section 3): `β = α - (r-1) 1_i + 1_(e \ {i})`, written additively
to avoid truncated subtraction. -/
def ToppleStep (r : ℕ) (i : ℕ) (e : Finset ℕ) (α β : ℕ →₀ ℕ) : Prop :=
  β + Finsupp.single i (r - 1) = α + ∑ j ∈ e.erase i, Finsupp.single j 1

/-- A monomial `x^α` of degree `d` is reduced (Section 2.1) when exactly one
vertex `i` has `α_i ≥ r - 1`. -/
def IsReducedMon (r : ℕ) (E : EdgeSet) (α : ℕ →₀ ℕ) : Prop :=
  ((vertices E).filter fun i => r - 1 ≤ α i).card = 1

open scoped Classical in
/-- The transfer matrix `C` on the degree-`d` monomials: entry `(α, β)` counts the
edges `e` at the class vertex `i` of `α` that topple `α` to `β`.  The Macaulay
matrix of the eigenvalue system is `λ I - C`. -/
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
/-- The restriction `C'` of the transfer matrix to the non-reduced monomials. -/
noncomputable def toppleMatrixNonReduced (r : ℕ) (E : EdgeSet) :
    Matrix ↥(nonReducedMonomials r E) ↥(nonReducedMonomials r E) ℤ :=
  Matrix.of fun a b =>
    ((E.filter fun e =>
      monClass r E a.1 ∈ e ∧ ToppleStep r (monClass r E a.1) e a.1 b.1).card : ℤ)

/-- The characteristic polynomial `phi_T` of the adjacency tensor, via the Macaulay
formula `Res = D_n / D'_n` (Proposition 2.3): the quotient of `det(λ I - C)` by the
monic `det(λ I - C')` under polynomial division. -/
noncomputable def charPoly (r : ℕ) (E : EdgeSet) : Polynomial ℤ := by
  classical
  exact (toppleMatrix r E).charpoly.divByMonic (toppleMatrixNonReduced r E).charpoly

end UniformHypertree

open UniformHypertree in
/-- Theorem 4.10 of Li–Su–Fallat, arXiv:2306.16247: for an `r`-tree `T` with `r ≥ 2`,
`phi_T = ∏_H phi_H ^ a_H` over the connected subgraphs `H` of `T`.  The first product
is over the single vertices `({v}, ∅)`, with `phi_H = λ`, `e(H) = 0` and `|bd(H)| = deg v`. -/
theorem P096 {r : ℕ} (hr : 2 ≤ r) {E : EdgeSet}
    (hT : IsRTree r E) :
    charPoly r E
      = (∏ v ∈ vertices E,
          (Polynomial.X : Polynomial ℤ) ^ aExp r E.card 0 (degree E v))
        * ∏ F ∈ connectedSubgraphs E,
            matchingPoly r F ^ aExp r E.card F.card (boundary E F).card := by
  sorry
