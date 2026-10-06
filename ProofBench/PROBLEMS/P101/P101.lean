import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Minimal

/- ---------------------------------------------------- -/
/- Paper: CONFORMAL HYPERGRAPHS: DUALITY AND IMPLICATIONS FOR THE UPPER CLIQUE TRANSVERSAL PROBLEM -/
/- ---------------------------------------------------- -/

/-!
# Upper clique transversals via dual conformality

This file formalizes the mathematical content of Theorem 4.1 of Boros, Gurvich,
Milanič and Uno, the paper's main graph-algorithmic application.

Theorem 4.1 reads: *for every integer `k ≥ 2`, given a graph `G = (V, E)`, the
`k`-Upper Clique Transversal problem is solvable in time `O(|V|^(3k-3))`.*  The
proof exhibits one algorithm and establishes two separate things about it:

* a **decision rule** — a purely combinatorial criterion, evaluated by the
  algorithm, that holds exactly on the yes-instances `τ_c⁺(G) ≥ k`;
* a **running-time estimate** for evaluating that rule.

The decision rule is the mathematical statement; it is what
`P101` below asserts.  Writing `ℋ` for the
hypergraph whose hyperedges are the minimal clique transversals of `G` of size
less than `k`, the rule is

  `τ_c⁺(G) ≥ k`  ⟺  `G ≠ G(ℋ^d)` or `ℋ^d` is not conformal,

which is Lemma 4.6 applied with the bound `k - 1`.

The running-time estimate is a claim about a machine model, not about graphs,
and it is **deliberately not encoded**, in line with the rest of this
development, where algorithmic and explicitness clauses are never asserted.
Encoding it would require a cost semantics (a fixed alphabet, unit-cost
transitions and an input encoding whose preparation is itself charged for);
an unconstrained `∃ machine, ∃ constant, …` statement carries no content,
because such a machine may compute the answer while initializing and halt after
zero steps.

## Dependency map

* Fact 2.1: blocker duality, `(ℋ^d)^d = ℋ` for Sperner `ℋ`.
* Theorem 2.6: a Sperner hypergraph is conformal iff it is the clique
  hypergraph of its co-occurrence graph.
* Lemma 2.7: the co-occurrence graph is determined by the hypergraph.
* Proposition 3.1 and Observation 3.2: dually conformal Sperner hypergraphs are
  exactly the families of minimal clique transversals of graphs.
* Lemma 4.2, Corollary 4.3, Proposition 4.7: the combinatorics of clique
  transversals; formalized and proved in `P041_LB.lean`.
* Lemma 4.6: the characterization of `τ_c⁺(G) ≤ k`; formalized in
  `P041_UB.lean`, where it is also shown to imply the main theorem.

## Reuse of existing definitions

`SimpleGraph.IsClique` and the order-theoretic `Maximal` / `Minimal` predicates
of Mathlib are reused; a maximal clique is `Maximal` for `IsClique` and a
minimal transversal is `Minimal` for `IsTransversal`, exactly as in the paper.
Hypergraphs, duality, conformality and the co-occurrence graph have no Mathlib
counterpart and are introduced here.
-/

namespace UpperCliqueTransversal

universe u

variable {V : Type u}

/-! ## Hypergraphs, duality and conformality -/

/-- A hypergraph on the vertex type `V`, presented by its family of hyperedges.

The paper's hypergraphs carry a vertex set; here the vertex set is the ambient
type `V`, so that a hypergraph is determined by its hyperedges alone. -/
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

theorem cooccurrenceGraph_adj (H : Hypergraph V) (u v : V) :
    (cooccurrenceGraph H).Adj u v ↔ u ≠ v ∧ ∃ e ∈ H, u ∈ e ∧ v ∈ e :=
  Iff.rfl

/-- `H` is conformal: whenever every pair of vertices of a set `U` lies in a
common hyperedge, the whole of `U` lies in a hyperedge. -/
def Conformal (H : Hypergraph V) : Prop :=
  ∀ U : Finset V, (∀ u ∈ U, ∀ v ∈ U, ∃ e ∈ H, u ∈ e ∧ v ∈ e) → ∃ e ∈ H, U ⊆ e

/-- `H` is dually conformal: its dual hypergraph `H^d` is conformal.  This is the
property studied throughout the paper. -/
def DuallyConformal (H : Hypergraph V) : Prop :=
  Conformal (dual H)

/-- `H` is Sperner: no hyperedge is contained in another. -/
def Sperner (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ⊆ f → e = f

/-- **Observation 2.5.** Every hyperedge of `H` is a clique of the co-occurrence
graph `G(H)`. -/
theorem isClique_cooccurrenceGraph_of_mem {H : Hypergraph V} {e : Finset V}
    (he : e ∈ H) : (cooccurrenceGraph H).IsClique (e : Set V) := by
  intro u hu v hv huv
  exact ⟨huv, e, he, Finset.mem_coe.mp hu, Finset.mem_coe.mp hv⟩

/-- The dual hypergraph is always Sperner: minimal transversals form an
antichain.  This is the easy half of the duality picture of Section 1. -/
theorem sperner_dual (H : Hypergraph V) : Sperner (dual H) := by
  intro e he f hf hef
  exact Finset.Subset.antisymm hef (hf.2 he.1 hef)

/-! ## Clique transversals of a graph -/

/-- The clique hypergraph of `G`: its hyperedges are the maximal cliques of `G`. -/
def cliqueHypergraph (G : SimpleGraph V) : Hypergraph V :=
  {C | Maximal (fun D : Finset V => G.IsClique (D : Set V)) C}

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

theorem IsMinimalCliqueTransversal.isCliqueTransversal {G : SimpleGraph V}
    {T : Finset V} (hT : IsMinimalCliqueTransversal G T) : IsCliqueTransversal G T :=
  hT.1

/-- The dual of the clique hypergraph is the family of all minimal clique
transversals.  This is the identification used throughout Sections 3 and 4. -/
theorem dual_cliqueHypergraph (G : SimpleGraph V) :
    dual (cliqueHypergraph G) = {T | IsMinimalCliqueTransversal G T} :=
  rfl

/-! ## The upper clique transversal number -/

/-- `τ_c⁺(G) ≥ k`: the yes-instances of the `k`-Upper Clique Transversal problem,
that is, the graphs admitting a minimal clique transversal of size at least `k`. -/
def HasLargeMinimalCliqueTransversal (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ T : Finset V, IsMinimalCliqueTransversal G T ∧ k ≤ T.card

/-- `τ_c⁺(G) ≤ k`: every minimal clique transversal of `G` has size at most `k`. -/
def UpperCliqueTransversalNumberAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ T : Finset V, IsMinimalCliqueTransversal G T → T.card ≤ k

/-- The two bounds are complementary, as they should be for a number. -/
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

/-! ## The hypergraph computed by the algorithm of Theorem 4.1 -/

/-- Step 1 of the algorithm of Theorem 4.1: the hypergraph on `V` whose
hyperedges are the minimal clique transversals of `G` of size less than `k`. -/
def smallMinimalCliqueTransversals (G : SimpleGraph V) (k : ℕ) : Hypergraph V :=
  {T | IsMinimalCliqueTransversal G T ∧ T.card < k}

theorem mem_smallMinimalCliqueTransversals {G : SimpleGraph V} {k : ℕ}
    {T : Finset V} :
    T ∈ smallMinimalCliqueTransversals G k ↔
      IsMinimalCliqueTransversal G T ∧ T.card < k :=
  Iff.rfl

/-- Every hyperedge of the algorithm's hypergraph is a minimal clique transversal
of `G`, so the hypergraph is a subfamily of the dual of the clique hypergraph. -/
theorem smallMinimalCliqueTransversals_subset (G : SimpleGraph V) (k : ℕ) :
    smallMinimalCliqueTransversals G k ⊆ dual (cliqueHypergraph G) :=
  fun _ hT => hT.1

/-! ## Main theorem -/

variable [Fintype V]

/--
**Theorem 4.1** (Boros, Gurvich, Milanič, Uno), mathematical content.

Let `k ≥ 2` and let `ℋ` be the hypergraph whose hyperedges are the minimal
clique transversals of `G` of size less than `k`.  Then `G` is a yes-instance of
the `k`-Upper Clique Transversal problem, that is `τ_c⁺(G) ≥ k`, precisely when
`ℋ` fails to be dually conformal or `G` differs from the co-occurrence graph of
`ℋ^d`.

This is the criterion the paper's algorithm evaluates: it accepts exactly when
one of the two conditions on the right-hand side is detected.  The paper derives
it from Lemma 4.6 with the bound `k - 1`; the derivation is carried out in
`P041_UB.lean`.

The bound `O(|V|^(3k-3))` on the cost of evaluating the criterion is a statement
about a machine model rather than about graphs, and is not asserted here; see
the module docstring.
-/
theorem P101 (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) :
    HasLargeMinimalCliqueTransversal G k ↔
      ¬ (DuallyConformal (smallMinimalCliqueTransversals G k) ∧
          cooccurrenceGraph (dual (smallMinimalCliqueTransversals G k)) = G) := by
  sorry

/-! ## Direct corollaries -/

/-- The decision rule in the branching form in which the algorithm of Theorem 4.1
is stated: accept if the graph differs from the co-occurrence graph of the dual,
and otherwise accept exactly when the dual fails to be conformal. -/
theorem kUpperCliqueTransversal_criterion_or (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) :
    HasLargeMinimalCliqueTransversal G k ↔
      cooccurrenceGraph (dual (smallMinimalCliqueTransversals G k)) ≠ G ∨
        ¬ DuallyConformal (smallMinimalCliqueTransversals G k) := by
  rw [P101 G k hk]
  tauto

/-- The no-instances of `k`-Upper Clique Transversal are exactly the graphs for
which the algorithm's hypergraph is dually conformal and reproduces `G`. -/
theorem upperCliqueTransversalNumberAtMost_criterion (G : SimpleGraph V) (k : ℕ)
    (hk : 2 ≤ k) :
    UpperCliqueTransversalNumberAtMost G (k - 1) ↔
      DuallyConformal (smallMinimalCliqueTransversals G k) ∧
        cooccurrenceGraph (dual (smallMinimalCliqueTransversals G k)) = G := by
  have hk1 : k - 1 + 1 = k := by omega
  rw [upperCliqueTransversalNumberAtMost_iff_not_hasLarge, hk1,
    P101 G k hk, not_not]

end UpperCliqueTransversal
