import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Minimal

namespace UpperCliqueTransversal

universe u

variable {V : Type u}

/-- A hypergraph on the vertex set `V` (the ambient type), given by its family of
hyperedges. -/
abbrev Hypergraph (V : Type u) : Type u := Set (Finset V)

/-- A transversal of `H`: a set of vertices intersecting every hyperedge. -/
def IsTransversal (H : Hypergraph V) (T : Finset V) : Prop :=
  ∀ e ∈ H, ∃ v ∈ T, v ∈ e

/-- A minimal transversal of `H`: a transversal containing no other transversal. -/
def IsMinimalTransversal (H : Hypergraph V) (T : Finset V) : Prop :=
  Minimal (IsTransversal H) T

/-- The dual (blocker) hypergraph `H^d`, whose hyperedges are exactly the
minimal transversals of `H`. -/
def dual (H : Hypergraph V) : Hypergraph V :=
  {T | IsMinimalTransversal H T}

/-- The co-occurrence graph `G(H)`: two distinct vertices are adjacent when some
hyperedge of `H` contains both. -/
def cooccurrenceGraph (H : Hypergraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e ∈ H, u ∈ e ∧ v ∈ e
  symm := ⟨by
    intro u v h
    obtain ⟨hne, e, heH, hu, hv⟩ := h
    exact ⟨hne.symm, e, heH, hv, hu⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

/-- Adjacency in the co-occurrence graph. -/
theorem cooccurrenceGraph_adj (H : Hypergraph V) (u v : V) :
    (cooccurrenceGraph H).Adj u v ↔ u ≠ v ∧ ∃ e ∈ H, u ∈ e ∧ v ∈ e :=
  Iff.rfl

/-- `H` is conformal: whenever every two distinct vertices of a set `U` lie in a
common hyperedge, the whole of `U` lies in a hyperedge.  Taking `U = ∅` and singletons,
a conformal hypergraph has a hyperedge and covers every vertex of `V`. -/
def Conformal (H : Hypergraph V) : Prop :=
  ∀ U : Finset V, (∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∃ e ∈ H, u ∈ e ∧ v ∈ e) → ∃ e ∈ H, U ⊆ e

/-- `H` is dually conformal: its dual hypergraph `H^d` is conformal. -/
def DuallyConformal (H : Hypergraph V) : Prop :=
  Conformal (dual H)

/-- `H` is Sperner: no hyperedge is contained in another. -/
def Sperner (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ⊆ f → e = f

/-- Observation 2.5: every hyperedge of `H` is a clique of `G(H)`. -/
theorem isClique_cooccurrenceGraph_of_mem {H : Hypergraph V} {e : Finset V}
    (he : e ∈ H) : (cooccurrenceGraph H).IsClique (e : Set V) := by
  intro u hu v hv huv
  exact ⟨huv, e, he, Finset.mem_coe.mp hu, Finset.mem_coe.mp hv⟩

/-- The dual hypergraph is always Sperner. -/
theorem sperner_dual (H : Hypergraph V) : Sperner (dual H) := by
  intro e he f hf hef
  exact Finset.Subset.antisymm hef (hf.2 he.1 hef)

/-- The clique hypergraph of `G`: its hyperedges are the maximal cliques of `G`. -/
def cliqueHypergraph (G : SimpleGraph V) : Hypergraph V :=
  {C | Maximal (fun D : Finset V => G.IsClique (D : Set V)) C}

/-- Membership in the clique hypergraph. -/
theorem mem_cliqueHypergraph {G : SimpleGraph V} {C : Finset V} :
    C ∈ cliqueHypergraph G ↔ Maximal (fun D : Finset V => G.IsClique (D : Set V)) C :=
  Iff.rfl

/-- A clique transversal of `G`: a set of vertices intersecting every maximal
clique of `G`. -/
def IsCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  IsTransversal (cliqueHypergraph G) T

/-- A minimal clique transversal of `G`: a clique transversal containing no other
clique transversal. -/
def IsMinimalCliqueTransversal (G : SimpleGraph V) (T : Finset V) : Prop :=
  Minimal (IsCliqueTransversal G) T

/-- A minimal clique transversal is a clique transversal. -/
theorem IsMinimalCliqueTransversal.isCliqueTransversal {G : SimpleGraph V}
    {T : Finset V} (hT : IsMinimalCliqueTransversal G T) : IsCliqueTransversal G T :=
  hT.1

/-- The dual of the clique hypergraph is the family of minimal clique transversals. -/
theorem dual_cliqueHypergraph (G : SimpleGraph V) :
    dual (cliqueHypergraph G) = {T | IsMinimalCliqueTransversal G T} :=
  rfl

/-- `τ_c⁺(G) ≥ k`: `G` has a minimal clique transversal of size at least `k` (a
yes-instance of `k`-Upper Clique Transversal). -/
def HasLargeMinimalCliqueTransversal (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ T : Finset V, IsMinimalCliqueTransversal G T ∧ k ≤ T.card

/-- `τ_c⁺(G) ≤ k`: every minimal clique transversal of `G` has size at most `k`. -/
def UpperCliqueTransversalNumberAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ T : Finset V, IsMinimalCliqueTransversal G T → T.card ≤ k

/-- `τ_c⁺(G) ≤ k` iff not `τ_c⁺(G) ≥ k + 1`. -/
theorem upperCliqueTransversalNumberAtMost_iff_not_hasLarge (G : SimpleGraph V)
    (k : ℕ) :
    UpperCliqueTransversalNumberAtMost G k ↔
      ¬ HasLargeMinimalCliqueTransversal G (k + 1) := by
  constructor
  · rintro h ⟨T, hT, hcard⟩
    exact absurd (h T hT) (by omega)
  · intro h T hT
    by_contra hc
    exact h ⟨T, hT, by omega⟩

/-- Lowering the threshold weakens the yes-instance condition. -/
theorem hasLargeMinimalCliqueTransversal_mono {G : SimpleGraph V} {k ℓ : ℕ}
    (hℓk : ℓ ≤ k) (h : HasLargeMinimalCliqueTransversal G k) :
    HasLargeMinimalCliqueTransversal G ℓ := by
  obtain ⟨T, hT, hkT⟩ := h
  exact ⟨T, hT, hℓk.trans hkT⟩

/-- The hypergraph `ℋ` of Theorem 4.1: its hyperedges are the minimal clique
transversals of `G` of size less than `k`. -/
def smallMinimalCliqueTransversals (G : SimpleGraph V) (k : ℕ) : Hypergraph V :=
  {T | IsMinimalCliqueTransversal G T ∧ T.card < k}

/-- Membership in `smallMinimalCliqueTransversals`. -/
theorem mem_smallMinimalCliqueTransversals {G : SimpleGraph V} {k : ℕ}
    {T : Finset V} :
    T ∈ smallMinimalCliqueTransversals G k ↔
      IsMinimalCliqueTransversal G T ∧ T.card < k :=
  Iff.rfl

/-- `ℋ` is a subfamily of the dual of the clique hypergraph. -/
theorem smallMinimalCliqueTransversals_subset (G : SimpleGraph V) (k : ℕ) :
    smallMinimalCliqueTransversals G k ⊆ dual (cliqueHypergraph G) :=
  fun _ hT => hT.1

variable [Fintype V]

/-- Theorem 4.1 of Boros–Gurvich–Milanič–Uno, arXiv:2309.00098, without its running time:
for `k ≥ 2`, with `ℋ` the minimal clique transversals of `G` of size less than `k`,
`τ_c⁺(G) ≥ k` iff `ℋ` is not dually conformal or `G` is not the co-occurrence graph of `ℋ^d`. -/
theorem P101 (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) :
    HasLargeMinimalCliqueTransversal G k ↔
      ¬ (DuallyConformal (smallMinimalCliqueTransversals G k) ∧
          cooccurrenceGraph (dual (smallMinimalCliqueTransversals G k)) = G) := by
  sorry

/-- Direct corollary: `τ_c⁺(G) ≥ k` iff `G(ℋ^d) ≠ G` or `ℋ` is not dually conformal. -/
theorem kUpperCliqueTransversal_criterion_or (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) :
    HasLargeMinimalCliqueTransversal G k ↔
      cooccurrenceGraph (dual (smallMinimalCliqueTransversals G k)) ≠ G ∨
        ¬ DuallyConformal (smallMinimalCliqueTransversals G k) := by
  rw [P101 G k hk]
  tauto

/-- Direct corollary: `τ_c⁺(G) ≤ k - 1` iff `ℋ` is dually conformal and `G = G(ℋ^d)`. -/
theorem upperCliqueTransversalNumberAtMost_criterion (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) :
    UpperCliqueTransversalNumberAtMost G (k - 1) ↔
      DuallyConformal (smallMinimalCliqueTransversals G k) ∧
        cooccurrenceGraph (dual (smallMinimalCliqueTransversals G k)) = G := by
  have hk1 : k - 1 + 1 = k := by omega
  rw [upperCliqueTransversalNumberAtMost_iff_not_hasLarge, hk1,
    P101 G k hk, not_not]

end UpperCliqueTransversal
