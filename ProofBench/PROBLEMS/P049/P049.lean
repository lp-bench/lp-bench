import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Hypergraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Order.Basic


open scoped BigOperators Hypergraph Topology
open Filter

namespace CountingPerfectMatchingsInDiracHypergraphs

attribute [local instance] Classical.dec

/-- A hypergraph uses every vertex of its ambient finite type. -/
def IsSpanning {V : Type*} (G : Hypergraph V) : Prop :=
  V(G) = Set.univ

/-- Every edge of `G` has exactly `k` vertices. -/
def IsUniform {V : Type*} (k : ℕ) (G : Hypergraph V) : Prop :=
  ∀ e : Set V, e ∈ E(G) → Set.ncard e = k

/-- The finite set of edges of a hypergraph on a finite vertex type. -/
noncomputable def edgeFinset {V : Type*} [Fintype V]
    (G : Hypergraph V) : Finset (Set V) := by
  classical
  exact Finset.univ.filter fun e => e ∈ E(G)

/-- Membership in `edgeFinset` is membership in the edge set. -/
@[simp] theorem mem_edgeFinset {V : Type*} [Fintype V]
    (G : Hypergraph V) (e : Set V) :
    e ∈ edgeFinset G ↔ e ∈ E(G) := by
  classical
  simp [edgeFinset]

/-- All `d`-element subsets of a finite vertex type. -/
noncomputable def dSubsets (V : Type*) [Fintype V] (d : ℕ) : Finset (Set V) := by
  classical
  exact Finset.univ.filter fun S => Set.ncard S = d

/-- Membership in `dSubsets V d` means having exactly `d` elements. -/
@[simp] theorem mem_dSubsets {V : Type*} [Fintype V] (d : ℕ) (S : Set V) :
    S ∈ dSubsets V d ↔ Set.ncard S = d := by
  classical
  simp [dSubsets]

/-- The number of edges of `G` containing the prescribed vertex set `S`. -/
noncomputable def degreeAt {V : Type*} [Fintype V]
    (G : Hypergraph V) (S : Set V) : ℕ := by
  exact ((edgeFinset G).filter fun e => S ⊆ e).card

/--
The minimum `d`-degree `δ_d(G)`.  The edge count is added as an upper
sentinel so that the minimum is always defined; whenever a `d`-set exists,
this is the usual minimum of the degrees of `d`-sets.
-/
noncomputable def minimumDdegree {V : Type*} [Fintype V]
    (G : Hypergraph V) (d : ℕ) : ℕ := by
  classical
  let degrees := (dSubsets V d).image (degreeAt G)
  exact (insert (edgeFinset G).card degrees).min' (by simp)

/-- The minimum `d`-degree is at most the degree of every `d`-set. -/
theorem minimumDdegree_le_degreeAt {V : Type*} [Fintype V]
    (G : Hypergraph V) {d : ℕ} {S : Set V} (hS : Set.ncard S = d) :
    minimumDdegree G d ≤ degreeAt G S := by
  apply Finset.min'_le
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_image.mpr
  exact ⟨S, (mem_dSubsets d S).mpr hS, rfl⟩

/-- A finite collection of pairwise disjoint edges covering every vertex. -/
def IsPerfectMatching {V : Type*} (G : Hypergraph V)
    (M : Finset (Set V)) : Prop :=
  (∀ e ∈ M, e ∈ E(G)) ∧
    (M : Set (Set V)).PairwiseDisjoint id ∧
      ⋃₀ (M : Set (Set V)) = V(G)

/-- The finite set of all perfect matchings of `G`. -/
noncomputable def perfectMatchings {V : Type*} [Fintype V]
    (G : Hypergraph V) : Finset (Finset (Set V)) := by
  classical
  exact Finset.univ.filter (IsPerfectMatching G)

/-- Membership in `perfectMatchings G` is being a perfect matching. -/
@[simp] theorem mem_perfectMatchings {V : Type*} [Fintype V]
    (G : Hypergraph V) (M : Finset (Set V)) :
    M ∈ perfectMatchings G ↔ IsPerfectMatching G M := by
  classical
  simp [perfectMatchings]

/-- Definition 2.2: `Φ(G)`, the number of perfect matchings in `G`. -/
noncomputable def perfectMatchingCount {V : Type*} [Fintype V]
    (G : Hypergraph V) : ℕ :=
  (perfectMatchings G).card

/--
Definition 1.1: a fractional perfect matching.  Weights are zero off the edge
set, lie in `[0,1]` on every edge, and sum to one around each vertex.
-/
structure FractionalPerfectMatching {V : Type*} [Fintype V]
    (G : Hypergraph V) where
  weight : Set V → ℝ
  zero_of_not_edge : ∀ e : Set V, e ∉ E(G) → weight e = 0
  weight_nonneg : ∀ e : Set V, 0 ≤ weight e
  weight_le_one : ∀ e : Set V, e ∈ E(G) → weight e ≤ 1
  vertex_sum : ∀ v ∈ V(G),
    (∑ e ∈ edgeFinset G, (if v ∈ e then weight e else 0)) = 1

namespace FractionalPerfectMatching

/-- The summand `x log(1/x)`, with the convention that it is zero at `x = 0`. -/
noncomputable def entropySummand (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log (1 / x)

/-- Definition 1.2: entropy of a fractional perfect matching. -/
noncomputable def entropy {V : Type*} [Fintype V] {G : Hypergraph V}
    (x : FractionalPerfectMatching G) : ℝ :=
  ∑ e ∈ edgeFinset G, entropySummand (x.weight e)

end FractionalPerfectMatching

/-- Definition 1.2: `h(G)`, the supremum of fractional-perfect-matching entropies. -/
noncomputable def hypergraphEntropy {V : Type*} [Fintype V]
    (G : Hypergraph V) : ℝ :=
  sSup {h : ℝ | ∃ x : FractionalPerfectMatching G, x.entropy = h}

/-- A degree bound forces a perfect matching in every spanning `k`-graph. -/
def ForcesPerfectMatching (d k n threshold : ℕ) : Prop :=
  ∀ G : Hypergraph (Fin n),
    IsSpanning G →
      IsUniform k G →
        threshold ≤ minimumDdegree G d →
          ∃ M : Finset (Set (Fin n)), IsPerfectMatching G M

/-- Definition 1.6: the finite perfect-matching Dirac threshold `m_d(k,n)`. -/
noncomputable def diracThreshold (d k n : ℕ) : ℕ :=
  sInf {threshold : ℕ | ForcesPerfectMatching d k n threshold}

/--
The number `α` is the asymptotic Dirac threshold `α_d(k)` of Definition 1.6.
The limit is taken along `n = k*m`, i.e. along integers divisible by `k`.
-/
def IsAsymptoticDiracThreshold (d k : ℕ) (α : ℝ) : Prop :=
  Tendsto
    (fun m : ℕ =>
      (diracThreshold d k (k * m) : ℝ) /
        (Nat.choose (k * m - d) (k - d) : ℝ))
    atTop (𝓝 α)

/-- Definition 2.1, eventually in `m`, for a family with `n = k*m` vertices. -/
def IsDiracFamily (d k : ℕ) (γ α : ℝ)
    (G : (m : ℕ) → Hypergraph (Fin (k * m))) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    IsSpanning (G m) ∧
      IsUniform k (G m) ∧
        (α + γ) * (Nat.choose (k * m - d) (k - d) : ℝ) ≤
          (minimumDdegree (G m) d : ℝ)

/--
The normalized logarithmic error `(log Φ(G) - h(G) + (1-1/k)n)/n`.  Its
convergence to zero is equivalent to `Φ(G) = e^{h(G)} (1/e + o(1))^{(1-1/k)n}`.
-/
noncomputable def normalizedCountingError {V : Type*} [Fintype V]
    (k : ℕ) (G : Hypergraph V) : ℝ :=
  (Real.log (perfectMatchingCount G : ℝ) - hypergraphEntropy G +
      (1 - 1 / (k : ℝ)) * (Fintype.card V : ℝ)) /
    (Fintype.card V : ℝ)

/-- The conclusion of Theorem 1.7 for a family indexed by `n = k*m`. -/
def HasEntropyCountingAsymptotic (k : ℕ)
    (G : (m : ℕ) → Hypergraph (Fin (k * m))) : Prop :=
  Tendsto (fun m => normalizedCountingError k (G m)) atTop (𝓝 0)

/--
For `1 ≤ d < k` and `γ > 0`, every family of `k`-graphs with minimum
`d`-degree at least `(α_d(k)+γ) * choose (n-d) (k-d)` has
`e^{h(G)} (1/e + o(1))^{(1-1/k)n}` perfect matchings.
Theorem 1.7 of Kwan–Safavi–Wang, arXiv:2408.09589.
-/
theorem P049
    (d k : ℕ) (hd : 1 ≤ d) (hdk : d < k)
    (γ α : ℝ) (hγ : 0 < γ)
    (hα : IsAsymptoticDiracThreshold d k α)
    (G : (m : ℕ) → Hypergraph (Fin (k * m)))
    (hG : IsDiracFamily d k γ α G) :
    HasEntropyCountingAsymptotic k G := by
  sorry

end CountingPerfectMatchingsInDiracHypergraphs
