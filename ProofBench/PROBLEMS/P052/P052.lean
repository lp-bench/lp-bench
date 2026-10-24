import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Data.Finset.Powerset


open scoped Hypergraph

namespace CliquesInHypergraphs

attribute [local instance] Classical.dec

/-- The hypergraph uses every vertex of its finite ambient type. -/
def IsSpanning {V : Type*} (H : Hypergraph V) : Prop :=
  V(H) = Set.univ

/-- Every edge has cardinality `k`. -/
def IsUniform {V : Type*} (k : ℕ) (H : Hypergraph V) : Prop :=
  ∀ e ∈ E(H), Set.ncard e = k

/--
A finite vertex set is complete when all its `k`-subsets are edges.  Sets with
fewer than `k` vertices are complete vacuously.
-/
def IsCompleteSet {V : Type*} (k : ℕ) (H : Hypergraph V)
    (S : Finset V) : Prop :=
  (S : Set V) ⊆ V(H) ∧
    ∀ e : Set V, e ⊆ (S : Set V) → Set.ncard e = k → e ∈ E(H)

/-- A clique is an inclusion-maximal complete vertex set. -/
def IsClique {V : Type*} (k : ℕ) (H : Hypergraph V)
    (S : Finset V) : Prop :=
  IsCompleteSet k H S ∧
    ∀ T : Finset V,
      S ⊆ T → IsCompleteSet k H T → T ⊆ S

/-- The finite family of all cliques. -/
noncomputable def cliques {V : Type*} [Fintype V]
    (k : ℕ) (H : Hypergraph V) : Finset (Finset V) :=
  Finset.univ.filter (IsClique k H)

/-- Membership in `cliques k H` is being a clique. -/
@[simp] theorem mem_cliques {V : Type*} [Fintype V]
    (k : ℕ) (H : Hypergraph V) (S : Finset V) :
    S ∈ cliques k H ↔ IsClique k H S := by
  simp [cliques]

/-- The set of distinct clique sizes occurring in `H`. -/
noncomputable def cliqueSizes {V : Type*} [Fintype V]
    (k : ℕ) (H : Hypergraph V) : Finset ℕ :=
  (cliques k H).image Finset.card

/-- `s` is a clique size when some clique has exactly `s` vertices. -/
@[simp] theorem mem_cliqueSizes {V : Type*} [Fintype V]
    (k : ℕ) (H : Hypergraph V) (s : ℕ) :
    s ∈ cliqueSizes k H ↔
      ∃ S : Finset V, IsClique k H S ∧ S.card = s := by
  simp [cliqueSizes]

/-- The number of different clique cardinalities. -/
noncomputable def distinctCliqueSizeCount {V : Type*} [Fintype V]
    (k : ℕ) (H : Hypergraph V) : ℕ :=
  (cliqueSizes k H).card

/-- Clique sizes lie between `0` and `|V|`. -/
theorem cliqueSizes_subset_range {V : Type*} [Fintype V]
    (k : ℕ) (H : Hypergraph V) :
    cliqueSizes k H ⊆ Finset.range (Fintype.card V + 1) := by
  intro s hs
  rcases (mem_cliqueSizes k H s).mp hs with ⟨S, _hS, rfl⟩
  simp only [Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.card_le_univ S)

/-- At most `|V|+1` clique sizes can occur. -/
theorem distinctCliqueSizeCount_le_card_add_one
    {V : Type*} [Fintype V] (k : ℕ) (H : Hypergraph V) :
    distinctCliqueSizeCount k H ≤ Fintype.card V + 1 := by
  unfold distinctCliqueSizeCount
  simpa using Finset.card_le_card (cliqueSizes_subset_range k H)

/--
For fixed `k ≥ 3` and `C`, every sufficiently large `n`-vertex `k`-uniform
hypergraph has at most `n - C` distinct clique sizes.  Theorem 1.1 of Gao,
arXiv:2510.14804; the case `k = 3` answers Erdős problem #775.
-/
theorem P052
    (k C : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : Hypergraph (Fin n),
        IsSpanning H → IsUniform k H →
          distinctCliqueSizeCount k H ≤ n - C := by
  sorry

end CliquesInHypergraphs
