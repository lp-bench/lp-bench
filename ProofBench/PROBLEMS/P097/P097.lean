import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# P097: The algebraic connectivity of token graphs

This file formalizes the token-graph core of

  X. Song, C. Dalfo, M. A. Fiol and S. Zhang, *On the algebraic connectivity of
  token graphs and graphs under perturbations*, arXiv:2412.21021.

The paper's dependency graph is:

* Section 2: the `k`-token graph `F_k(G)`, the `(n, k)`-binomial matrix `B`, the
  Laplacian `L(G)`, the algebraic connectivity `alpha(G) = lambda_2` and the
  Rayleigh quotient (2.1);
* Lemmas 2.1 and 2.2 (Horn-Johnson): eigenvalue interlacing;
* Lemmas 2.3-2.6: `alpha(G) = alpha(G + uv)` iff `G` has a Fiedler vector with
  `x_u = x_v`;
* **Lemma 2.7**: `(i)` if `x` is a `lambda`-eigenvector of `L(G)` then `Bx` is a
  `lambda`-eigenvector of `L(F_k(G))`, and `(ii)` the converse for `w` with
  `B^T w != 0`;
* **Theorem 2.8**: consequently the spectrum of `G` is contained in the spectrum
  of `F_k(G)`;
* Theorem 2.9, Lemma 2.10, Theorem 2.11: known families with
  `alpha(F_k(G)) = alpha(G)`;
* Sections 3-5: the new results, Theorem 3.1 onwards, on adding edges, kite
  graphs and graphs with a cut clique, culminating in **Theorem 5.3**: if `G`
  has a cut clique `K_r` of maximum possible degree `r(n - r)`, then
  `alpha(F_k(G)) = alpha(G) = r`.  For `r = 1` this recovers Theorem 2.11
  (Barik and Verma) on cut vertices of degree `n - 1`.

The target of the problem is the paper's main theorem, Theorem 5.3, stated at
the end of this file as `cutClique_tokenGraph_algConnectivity` and proved by
`sorry` -- the single `sorry` of the file.  Everything else below is proved
from first principles with no `sorry` and no new axioms.  The results
formalized in full are

* `tokenGraph`, the `k`-token graph of Section 2, with `tokenGraph_mono`, the
  spanning-subgraph relation `F_k(G) <= F_k(G + uv)` used in (3.1);
* `binomLift`, the action `x |-> Bx` of the `(n, k)`-binomial matrix;
* `lapMatrix_mulVec_binomLift`, the intertwining identity
  `L(F_k(G)) B x = B L(G) x`, which is the content of **Lemma 2.7(i)**;
* `binomLift_eq_zero` and `binomLift_injective`: `B` has trivial kernel for
  `1 <= k <= n - 1`;
* `exists_eigenvector_tokenGraph`, which is **Theorem 2.8**: every Laplacian
  eigenvalue of `G` is a Laplacian eigenvalue of `F_k(G)`;
* `rayleighQuotient` and `algConnectivity`, the Rayleigh quotient (2.1) and the
  algebraic connectivity `alpha` it characterizes, needed to *state*
  Theorem 5.3.

The intermediate results of the paper that are not asserted here are the
eigenvalue-ordering results: Lemmas 2.1-2.6, Theorem 2.9 onwards, and the new
Theorems of Sections 3 and 4, all of which additionally need interlacing and
Fiedler vectors.

The proof of `lapMatrix_mulVec_binomLift` is the combinatorial one: the
neighbours of a `k`-set `A` in `F_k(G)` are exactly the moves `u -> v` along an
edge with `u` in `A` and `v` outside `A`, and the pairs internal to `A`
contribute an antisymmetric sum, which vanishes.
-/

namespace TokenGraph

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The Laplacian action -/

/-- The Laplacian acts by summing the differences along the edges at a vertex.
This is `SimpleGraph.lapMatrix_mulVec_apply` in the form used below. -/
theorem lapMatrix_mulVec_eq_sum {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (x : W → ℝ) (v : W) :
    (H.lapMatrix ℝ *ᵥ x) v = ∑ w ∈ H.neighborFinset v, (x v - x w) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]

/-! ## The `k`-token graph -/

/-- The vertices of the `k`-token graph: the `k`-subsets of `V`, that is, the
configurations of `k` indistinguishable tokens on distinct vertices. -/
abbrev TokenSet (V : Type*) (k : ℕ) := {A : Finset V // A.card = k}

/-- Two configurations are adjacent when one is obtained from the other by
moving a single token along an edge of `G` to an unoccupied vertex. -/
def TokenAdj (G : SimpleGraph V) (k : ℕ) (A B : TokenSet V k) : Prop :=
  ∃ u : V, ∃ v : V, G.Adj u v ∧ u ∈ A.1 ∧ v ∉ A.1 ∧ B.1 = insert v (A.1.erase u)

instance decidableTokenAdj (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (TokenAdj G k) := fun A B => by
  unfold TokenAdj
  infer_instance

omit [Fintype V] in
/-- Moving a token off an occupied vertex onto an unoccupied one preserves the
number of tokens. -/
theorem card_move {k : ℕ} (A : TokenSet V k) {u v : V} (hu : u ∈ A.1)
    (hv : v ∉ A.1) : (insert v (A.1.erase u)).card = k := by
  have hvne : v ∉ A.1.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  have hk : 1 ≤ k := by
    rw [← A.2]
    exact Finset.card_pos.mpr ⟨u, hu⟩
  rw [Finset.card_insert_of_notMem hvne, Finset.card_erase_of_mem hu, A.2]
  omega

/-- The `k`-token graph `F_k(G)` of Section 2. -/
def tokenGraph (G : SimpleGraph V) (k : ℕ) : SimpleGraph (TokenSet V k) where
  Adj := TokenAdj G k
  symm := ⟨by
    rintro A B ⟨u, v, hadj, huA, hvA, hB⟩
    refine ⟨v, u, hadj.symm, ?_, ?_, ?_⟩
    · rw [hB]
      exact Finset.mem_insert_self v _
    · rw [hB]
      intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hadj.ne h
      · exact (Finset.notMem_erase u A.1) h
    · rw [hB, Finset.erase_insert (fun h => hvA (Finset.mem_of_mem_erase h)),
        Finset.insert_erase huA]⟩
  loopless := ⟨by
    rintro A ⟨u, v, _, _, hvA, hB⟩
    exact hvA (by rw [hB]; exact Finset.mem_insert_self v _)⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (tokenGraph G k).Adj :=
  decidableTokenAdj G k

omit [Fintype V] in
theorem tokenGraph_adj {G : SimpleGraph V} {k : ℕ} {A B : TokenSet V k} :
    (tokenGraph G k).Adj A B ↔
      ∃ u : V, ∃ v : V, G.Adj u v ∧ u ∈ A.1 ∧ v ∉ A.1 ∧ B.1 = insert v (A.1.erase u) :=
  Iff.rfl

omit [Fintype V] in
/-- Adding edges to `G` adds edges to `F_k(G)`; in particular `F_k(G)` is a
spanning subgraph of `F_k(G + uv)`, which is the observation (3.1) of the
paper. -/
theorem tokenGraph_mono {G H : SimpleGraph V} (h : G ≤ H) (k : ℕ) :
    tokenGraph G k ≤ tokenGraph H k := by
  rintro A B ⟨u, v, hadj, huA, hvA, hB⟩
  exact ⟨u, v, h hadj, huA, hvA, hB⟩

/-! ## The binomial matrix -/

/-- The action of the `(n, k)`-binomial matrix `B`: the entry of `Bx` at a
`k`-set `A` is the sum of `x` over `A`. -/
def binomLift (k : ℕ) (x : V → ℝ) (A : TokenSet V k) : ℝ :=
  ∑ j ∈ A.1, x j

omit [Fintype V] in
/-- A single token move changes `Bx` by the difference of the two endpoints. -/
theorem binomLift_sub_binomLift {k : ℕ} (x : V → ℝ) (A B : TokenSet V k) {u v : V}
    (hu : u ∈ A.1) (hv : v ∉ A.1) (hB : B.1 = insert v (A.1.erase u)) :
    binomLift k x A - binomLift k x B = x u - x v := by
  have hvne : v ∉ A.1.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  rw [binomLift, binomLift, hB, Finset.sum_insert hvne, Finset.sum_erase_eq_sub hu]
  ring

omit [Fintype V] [DecidableEq V] in
theorem binomLift_smul {k : ℕ} (mu : ℝ) (x : V → ℝ) :
    binomLift k (mu • x) = mu • binomLift k x := by
  funext A
  simp only [binomLift, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-! ## Lemma 2.7(i): the binomial matrix intertwines the Laplacians -/

/-- The token moves available to `A`: ordered pairs `(u, v)` with `u` occupied,
`v` unoccupied and `uv` an edge of `G`. -/
def moves (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (V × V) :=
  (A ×ˢ (Finset.univ \ A)).filter fun p => G.Adj p.1 p.2

/-- The pairs of occupied vertices joined by an edge. -/
def internalPairs (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    Finset (V × V) :=
  (A ×ˢ A).filter fun p => G.Adj p.1 p.2

omit [Fintype V] [DecidableEq V] in
private theorem sum_filter_product {β M : Type*} [AddCommMonoid M]
    (s : Finset V) (t : Finset β) (P : V × β → Prop) [DecidablePred P]
    (f : V × β → M) :
    ∑ p ∈ (s ×ˢ t).filter P, f p
      = ∑ a ∈ s, ∑ b ∈ t.filter (fun b => P (a, b)), f (a, b) := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Finset.sum_filter]

omit [Fintype V] [DecidableEq V] in
/-- The sum of `x u - x v` over the pairs internal to `A` vanishes, because the
summand is antisymmetric and the index set is closed under swapping. -/
theorem sum_internalPairs_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (x : V → ℝ) :
    ∑ p ∈ internalPairs G A, (x p.1 - x p.2) = 0 := by
  classical
  have hmemswap : ∀ p : V × V, p ∈ internalPairs G A → p.swap ∈ internalPairs G A := by
    intro p hp
    obtain ⟨hprod, hadj⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hprod
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hadj.symm⟩
  have hself : (internalPairs G A).image Prod.swap = internalPairs G A := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro p hp
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      rw [← hqp]
      exact hmemswap q hq
    · intro p hp
      exact Finset.mem_image.mpr ⟨p.swap, hmemswap p hp, Prod.swap_swap p⟩
  have hswap : ∑ p ∈ internalPairs G A, (x p.1 - x p.2)
      = ∑ p ∈ internalPairs G A, (x p.2 - x p.1) := by
    conv_lhs => rw [← hself]
    rw [Finset.sum_image (fun a _ b _ h => Prod.swap_injective h)]
    exact Finset.sum_congr rfl fun p _ => rfl
  have hzero : ∑ p ∈ internalPairs G A, (x p.2 - x p.1)
      + ∑ p ∈ internalPairs G A, (x p.1 - x p.2) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun p _ => by ring
  linarith

/-- The neighbours of `A` in `F_k(G)` are in bijection with the token moves
available to `A`, and the corresponding differences of `Bx` are the differences
of `x` along the move. -/
theorem sum_neighborFinset_eq_sum_moves (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (x : V → ℝ) (A : TokenSet V k) :
    ∑ B ∈ (tokenGraph G k).neighborFinset A, (binomLift k x A - binomLift k x B)
      = ∑ p ∈ moves G A.1, (x p.1 - x p.2) := by
  classical
  refine (Finset.sum_bij
    (fun p (hp : p ∈ moves G A.1) =>
      (⟨insert p.2 (A.1.erase p.1), card_move A
        (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        (Finset.mem_sdiff.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2).2⟩ :
          TokenSet V k))
    ?_ ?_ ?_ ?_).symm
  · -- the image lies in the neighbourhood of `A`
    intro p hp
    obtain ⟨hprod, hadj⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprod
    rw [SimpleGraph.mem_neighborFinset]
    exact ⟨p.1, p.2, hadj, hp1, (Finset.mem_sdiff.mp hp2).2, rfl⟩
  · -- injectivity
    intro p hp q hq hpq
    obtain ⟨hprodp, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprodp
    obtain ⟨hprodq, _⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hprodq
    have hp2' : p.2 ∉ A.1 := (Finset.mem_sdiff.mp hp2).2
    have hq2' : q.2 ∉ A.1 := (Finset.mem_sdiff.mp hq2).2
    have heq : insert p.2 (A.1.erase p.1) = insert q.2 (A.1.erase q.1) :=
      congrArg Subtype.val hpq
    have hsnd : p.2 = q.2 := by
      have hmem : p.2 ∈ insert q.2 (A.1.erase q.1) := by
        rw [← heq]; exact Finset.mem_insert_self _ _
      rcases Finset.mem_insert.mp hmem with h | h
      · exact h
      · exact absurd (Finset.mem_of_mem_erase h) hp2'
    have hfst : p.1 = q.1 := by
      have hnot : p.1 ∉ insert p.2 (A.1.erase p.1) := by
        intro hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hp2' (h ▸ hp1)
        · exact (Finset.notMem_erase p.1 A.1) h
      rw [heq] at hnot
      by_contra hne
      exact hnot (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hne, hp1⟩))
    exact Prod.ext hfst hsnd
  · -- surjectivity
    intro B hB
    rw [SimpleGraph.mem_neighborFinset] at hB
    obtain ⟨u, v, hadj, huA, hvA, hBval⟩ := hB
    refine ⟨(u, v), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨huA, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvA⟩⟩, hadj⟩
    · exact Subtype.ext hBval.symm
  · -- the summands agree
    intro p hp
    obtain ⟨hprod, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprod
    exact (binomLift_sub_binomLift x A _ hp1 (Finset.mem_sdiff.mp hp2).2 rfl).symm

/-- **Lemma 2.7(i), in matrix form.**  The binomial matrix intertwines the two
Laplacians: `L(F_k(G)) B x = B L(G) x` for every `x`.  Consequently `B` carries
`lambda`-eigenvectors of `L(G)` to `lambda`-eigenvectors of `L(F_k(G))`. -/
theorem lapMatrix_mulVec_binomLift (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (x : V → ℝ) (A : TokenSet V k) :
    ((tokenGraph G k).lapMatrix ℝ *ᵥ binomLift k x) A
      = binomLift k (G.lapMatrix ℝ *ᵥ x) A := by
  classical
  rw [lapMatrix_mulVec_eq_sum, sum_neighborFinset_eq_sum_moves]
  -- the right-hand side splits into moves out of `A` and pairs inside `A`
  have hR : binomLift k (G.lapMatrix ℝ *ᵥ x) A
      = ∑ u ∈ A.1, ∑ w ∈ G.neighborFinset u, (x u - x w) := by
    rw [binomLift]
    exact Finset.sum_congr rfl fun u _ => lapMatrix_mulVec_eq_sum G x u
  rw [hR]
  have hsplit : ∀ u : V, ∑ w ∈ G.neighborFinset u, (x u - x w)
      = ∑ w ∈ (Finset.univ \ A.1).filter (fun w => G.Adj u w), (x u - x w)
        + ∑ w ∈ A.1.filter (fun w => G.Adj u w), (x u - x w) := by
    intro u
    have hpart : G.neighborFinset u
        = (Finset.univ \ A.1).filter (fun w => G.Adj u w)
          ∪ A.1.filter (fun w => G.Adj u w) := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · intro hw
        by_cases hA : w ∈ A.1
        · exact Or.inr ⟨hA, hw⟩
        · exact Or.inl ⟨hA, hw⟩
      · rintro (⟨-, hw⟩ | ⟨-, hw⟩) <;> exact hw
    have hdisj : Disjoint ((Finset.univ \ A.1).filter (fun w => G.Adj u w))
        (A.1.filter (fun w => G.Adj u w)) := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2
        (Finset.mem_filter.mp hw').1
    rw [hpart, Finset.sum_union hdisj]
  rw [Finset.sum_congr rfl fun u (_ : u ∈ A.1) => hsplit u, Finset.sum_add_distrib]
  have hout : ∑ u ∈ A.1, ∑ w ∈ (Finset.univ \ A.1).filter (fun w => G.Adj u w), (x u - x w)
      = ∑ p ∈ moves G A.1, (x p.1 - x p.2) :=
    (sum_filter_product A.1 (Finset.univ \ A.1) (fun p => G.Adj p.1 p.2)
      (fun p => x p.1 - x p.2)).symm
  have hin : ∑ u ∈ A.1, ∑ w ∈ A.1.filter (fun w => G.Adj u w), (x u - x w)
      = ∑ p ∈ internalPairs G A.1, (x p.1 - x p.2) :=
    (sum_filter_product A.1 A.1 (fun p => G.Adj p.1 p.2)
      (fun p => x p.1 - x p.2)).symm
  rw [hout, hin, sum_internalPairs_eq_zero, add_zero]

/-- The eigenvector form of **Lemma 2.7(i)**. -/
theorem lapMatrix_mulVec_binomLift_smul (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (mu : ℝ) (x : V → ℝ) (hx : G.lapMatrix ℝ *ᵥ x = mu • x) :
    (tokenGraph G k).lapMatrix ℝ *ᵥ binomLift k x = mu • binomLift k x := by
  funext A
  rw [lapMatrix_mulVec_binomLift, hx, binomLift_smul]

/-! ## The binomial matrix has trivial kernel for `1 <= k <= n - 1` -/

omit [DecidableEq V] in
/-- If `Bz = 0` and `1 <= k < n`, then `z = 0`.  Two `k`-sets differing by one
token show that `z` is constant, and then any single `k`-set shows the constant
is zero. -/
theorem binomLift_eq_zero {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < Fintype.card V)
    {z : V → ℝ} (h : binomLift k z = 0) : z = 0 := by
  classical
  have hconst : ∀ u w : V, z u = z w := by
    intro u w
    by_cases huw : u = w
    · rw [huw]
    · -- choose a `k`-set containing `u` and avoiding `w`
      have hsub : ({u} : Finset V) ⊆ Finset.univ.erase w :=
        Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨huw, Finset.mem_univ u⟩)
      have hcard : k ≤ (Finset.univ.erase w).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]
        omega
      obtain ⟨S, huS, hSsub, hScard⟩ :=
        Finset.exists_subsuperset_card_eq hsub (by simpa using hk1) hcard
      have huS' : u ∈ S := huS (Finset.mem_singleton_self u)
      have hwS : w ∉ S := fun hw => (Finset.mem_erase.mp (hSsub hw)).1 rfl
      set A : TokenSet V k := ⟨S, hScard⟩ with hA
      set B : TokenSet V k := ⟨insert w (S.erase u), card_move A huS' hwS⟩ with hB
      have hdiff : binomLift k z A - binomLift k z B = z u - z w :=
        binomLift_sub_binomLift z A B huS' hwS rfl
      have hA0 : binomLift k z A = 0 := congrFun h A
      have hB0 : binomLift k z B = 0 := congrFun h B
      rw [hA0, hB0] at hdiff
      linarith
  -- now pick any `k`-set and read off the constant
  obtain ⟨S, -, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (n := k)
      (by rw [Finset.card_univ]; omega)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u₀, hu₀⟩ := hSne
  have hzero : binomLift k z (⟨S, hScard⟩ : TokenSet V k) = 0 :=
    congrFun h (⟨S, hScard⟩ : TokenSet V k)
  have hsum : binomLift k z (⟨S, hScard⟩ : TokenSet V k) = (k : ℝ) * z u₀ := by
    rw [binomLift]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ S) => hconst j u₀]
    rw [Finset.sum_const, hScard, nsmul_eq_mul]
  rw [hsum] at hzero
  have hk : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hu₀zero : z u₀ = 0 := by
    rcases mul_eq_zero.mp hzero with h1 | h2
    · exact absurd h1 hk
    · exact h2
  funext u
  rw [hconst u u₀, hu₀zero]
  rfl

omit [DecidableEq V] in
/-- For `1 <= k <= n - 1` the binomial matrix `B` is injective. -/
theorem binomLift_injective {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < Fintype.card V) :
    Function.Injective (binomLift (V := V) k) := by
  intro x y hxy
  have hz : binomLift k (x - y) = 0 := by
    funext A
    have hsub : binomLift k (x - y) A = binomLift k x A - binomLift k y A := by
      simp only [binomLift, Pi.sub_apply, Finset.sum_sub_distrib]
    rw [hsub, hxy]
    simp
  have hxy' : x - y = 0 := binomLift_eq_zero hk1 hk2 hz
  funext u
  have hu := congrFun hxy' u
  simp only [Pi.sub_apply, Pi.zero_apply] at hu
  linarith

/-! ## Theorem 2.8 -/

/-- **Theorem 2.8.**  For `1 <= k <= n - 1`, every Laplacian eigenvalue of `G` is
a Laplacian eigenvalue of its `k`-token graph `F_k(G)`: the spectrum of `G` is
contained in the spectrum of `F_k(G)`. -/
theorem exists_eigenvector_tokenGraph (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < Fintype.card V) (mu : ℝ) {x : V → ℝ}
    (hx : x ≠ 0) (heig : G.lapMatrix ℝ *ᵥ x = mu • x) :
    ∃ y : TokenSet V k → ℝ, y ≠ 0 ∧
      (tokenGraph G k).lapMatrix ℝ *ᵥ y = mu • y := by
  refine ⟨binomLift k x, ?_, lapMatrix_mulVec_binomLift_smul G k mu x heig⟩
  intro hzero
  exact hx (binomLift_eq_zero hk1 hk2 hzero)

/-! ## Algebraic connectivity -/

/-- The Rayleigh quotient (2.1) of the Laplacian of `H` at the vector `x`. -/
noncomputable def rayleighQuotient {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (x : W → ℝ) : ℝ :=
  (x ⬝ᵥ (H.lapMatrix ℝ *ᵥ x)) / (x ⬝ᵥ x)

/-- The algebraic connectivity `alpha(H) = lambda_2(L(H))` of Section 2, via
the variational characterization (2.1): the infimum of the Rayleigh quotient of
the Laplacian over the nonzero vectors orthogonal to the all-one vector.
Since the all-one vector spans an eigenspace of the smallest eigenvalue `0` of
the positive-semidefinite `L(H)`, this is the second-smallest Laplacian
eigenvalue whenever `H` has at least two vertices. -/
noncomputable def algConnectivity {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] : ℝ :=
  sInf {q : ℝ | ∃ x : W → ℝ, x ≠ 0 ∧ (∑ v : W, x v) = 0 ∧ rayleighQuotient H x = q}

/-! ## Theorem 5.3: the main theorem -/

end TokenGraph

open TokenGraph in
/-- **Theorem 5.3**, the main theorem of the paper.  Let `G` be a graph on `n`
vertices with a cut clique of maximum possible degree: a clique `S` on `r >= 1`
vertices that is joined to *all* vertices outside it (so `d_G(K_r) = r(n - r)`)
and whose removal leaves a disconnected graph -- the components
`G_1, ..., G_s`, `s >= 2`, of the paper, captured by the induced graph on the
complement of `S` not being preconnected.  Then, for every `k` with
`1 <= k <= n - 1`, the algebraic connectivities of `G` and of its `k`-token
graph `F_k(G)` are both equal to `r`.

For `r = 1` this is Theorem 2.11 (Barik and Verma): a cut vertex of degree
`n - 1` forces `alpha(F_k(G)) = alpha(G) = 1`.

This is the target statement of problem P097; its `sorry` is the only one in
the file. -/
theorem P097 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} (hr : 1 ≤ r)
    (S : Finset V) (hcard : S.card = r) (hclique : G.IsClique (S : Set V))
    (hdeg : ∀ u ∈ S, ∀ v ∉ S, G.Adj u v)
    (hcut : ¬ (G.induce ((S : Set V)ᶜ)).Preconnected)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < Fintype.card V) :
    algConnectivity G = r ∧ algConnectivity (tokenGraph G k) = r := by
  sorry
