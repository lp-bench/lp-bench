import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/- ---------------------------------------------------- -/
/- Paper: Perfect Matchings in the Semi-Random Graph Process -/
/- ---------------------------------------------------- -/

/-!
# P048: Perfect matchings in the semi-random graph process

This file formalizes the semi-random graph process of Section 1.1 and the main
theorem of

  P. Gao, C. MacRury and P. Prałat, *Perfect matchings in the semi-random
  graph process*, arXiv:2105.13455.

## The paper's dependency graph

* Section 1.1: the semi-random process.  In round `t` a square `u_t` is
  chosen uniformly at random from `[n]`, the player (aware of the graph and of
  `u_t`) selects a circle `v_t` and the edge `u_t v_t` is added.  A strategy
  is a family of distributions `f_t(u_1, v_1, …, u_{t-1}, v_{t-1}, u_t)` from
  which `v_t` is drawn.  For an increasing property `P` and `0 < q < 1`,
  `τ_P(S, q, n)` is the least `t` with `P[G_t ∈ P] ≥ q` (`∞` if there is
  none), `τ_P(q, n) = inf_S τ_P(S, q, n)` and
  `τ_P = lim_{q → 1⁻} limsup_{n → ∞} τ_P(q, n) / n`.
* Section 1.2: the property `PM` of having a perfect matching, where by
  convention a graph on an odd number of vertices has a perfect matching if
  some matching saturates all but one vertex.
* **Theorem 1.1**, the main theorem: `τ_PM ≤ β + 10⁻⁵ ≤ 1.20524`, where `β` is
  derived from a system of differential equations.
* Theorem 1.3, the second main result: `τ_PM ≥ α ≥ 0.93261`, where `α` is the
  root of the function `g` of (3); Proposition 1.2 is the earlier bound
  `τ_PM ≥ ln 2`.
* Section 2, the proof of Theorem 1.1: the warm-up algorithm of Section 2.1
  (differential equations (1)-(2), a.a.s. at most `εn` unsaturated vertices
  after `1.2769497 n` rounds, and the clean-up algorithm saturating them in at
  most `100 √ε n` further rounds), and the improved algorithm of Section 2.2
  analysed phase by phase (Propositions 2.1-2.2 by the differential equation
  method, Proposition 2.3: after `k = 1100` phases, a.a.s. `τ_k ≤ 1.20365 n`
  and `X(τ_k) ≥ (1 - 10⁻⁶) n`), followed by the randomised algorithm and the
  clean-up, `0.00158 n + 10⁻⁵ n` further rounds.
* Section 3, the proof of Theorem 1.3: Proposition 3.1 (the bridge from a.a.s.
  statements to lower bounds on `τ_P`), the approximate perfect matchings of
  Definition 3.2 and Propositions 3.3-3.4, Lemma 3.5, Proposition 3.6 and
  Lemma 3.7 (the differential equations for redundant and well-positioned
  vertices).

## What is formalized here

The target of the problem is **Theorem 1.1**, stated at the end of this file as
`P105` and proved by `sorry`, the single `sorry` of the file.
Everything else is proved from first principles with no `sorry` and no new
axiom:

* `singleEdge`, `addEdge`, `Play`, `IncreasingProperty`, `HasPerfectMatching`,
  `successProbability`: the deterministic interface of the first version of
  this file (realized plays, the underlying simple graph, perfect matchings and
  increasing properties), kept unchanged;
* `History`, `Strategy`, `historyGraph`: histories `(u_1, v_1, …, u_t, v_t)`,
  strategies as history-dependent distributions on the vertex set, and the
  underlying simple graph of a history (loops and multiplicities discarded);
* `step`, `playLawFrom`, `playLaw`: the law of the process, built round by
  round; `playLawFrom_add` is its Markov property;
* `successProbFrom`, `successProb`: `P[G_t ∈ P]`, monotone in `t` for an
  increasing property;
* `hittingTime`, `minHittingTime`, `tauAt`, `tau`: `τ_P(S, q, n)`, `τ_P(q, n)`,
  `limsup_n τ_P(q, n) / n` and `τ_P`, with `tendsto_tauAt` identifying the
  supremum over `0 < q < 1` with the paper's left limit;
* `tau_le_of_forall_exists_tendsto` and `le_tau_of_forall_eventually`: the
  bridges from a.a.s. statements to upper and lower bounds on `τ_P`, the
  latter being Proposition 3.1 of the paper;
* `HasNearPerfectMatching`, `perfectMatchingProperty`: the property `PM` with
  the paper's convention for odd `n`, an increasing property.

## What is deliberately not asserted

* The constant `β` of Theorem 1.1 is only characterised numerically in the
  paper (Maple worksheets); the theorem is stated with the printed bound
  `1.20524`.
* Theorem 1.3 and Proposition 1.2 are not stated, since the file carries a
  single `sorry`; the bridge lemma they use (Proposition 3.1) is proved.
* Nothing about the algorithms of Sections 2-3 is encoded.

## Conventions

* Strategies may answer with any vertex, as in Section 1.1; the paper's remark
  that one may restrict to strategies which do not create self-loops is not
  imposed (a larger class of strategies only makes the infimum smaller, and the
  paper defines `τ_P(q, n)` as the infimum over all strategies).
* `τ_P` uses the vertex sets `Fin (n + 1)`, i.e. `[n]` for `n ≥ 1`, as in the
  paper; probabilities `q` live in `ℝ≥0∞` and `τ_P(S, q, n)` in `ℕ∞`.
* `PM` is read with the paper's convention: a matching saturating all but at
  most one vertex.  On an even number of vertices this is a perfect matching
  in Mathlib's sense, since a matching saturates an even number of vertices.
-/

open MeasureTheory

noncomputable section

namespace PerfectMatchingSemiRandom

variable {V : Type*}

/-- The simple graph containing just the edge `u v`.  When `u = v`, the loop
is discarded, matching the paper's passage from a multigraph play to its
underlying simple graph. -/
def singleEdge (u v : V) : SimpleGraph V where
  Adj x y := Not (x = y) /\
    ((x = u /\ y = v) \/ (x = v /\ y = u))
  symm := ⟨by
    intro x y h
    rcases h with ⟨hxy, h⟩
    refine ⟨fun hyx => hxy hyx.symm, ?_⟩
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

/-- Add one semi-random edge and forget loops and multiplicities. -/
def addEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  G ⊔ singleEdge u v

theorem le_addEdge (G : SimpleGraph V) (u v : V) :
    G <= addEdge G u v :=
  le_sup_left

theorem singleEdge_le_addEdge (G : SimpleGraph V) (u v : V) :
    singleEdge u v <= addEdge G u v :=
  le_sup_right

/-- A length-`T` realized play.  The response may depend on the entire past
and on the current offered vertex; that dependence belongs to the strategy
which generates the play. -/
structure Play (V : Type*) (T : Nat) where
  offered : Fin T -> V
  response : Fin T -> V

instance playMeasurableSpace (V : Type*) (T : Nat) :
    MeasurableSpace (Play V T) := ⊤

/-- The underlying simple graph produced by all rounds of a play. -/
def Play.graph {T : Nat} (play : Play V T) : SimpleGraph V :=
  ⨆ t : Fin T, singleEdge (play.offered t) (play.response t)

theorem Play.singleEdge_le_graph {T : Nat} (play : Play V T) (t : Fin T) :
    singleEdge (play.offered t) (play.response t) <= play.graph := by
  exact le_iSup (fun i : Fin T =>
    singleEdge (play.offered i) (play.response i)) t

/-- A graph property is increasing if adding edges preserves it. -/
def IncreasingProperty (property : SimpleGraph V -> Prop) : Prop :=
  forall G H, G <= H -> property G -> property H

theorem IncreasingProperty.trans
    {P Q : SimpleGraph V -> Prop}
    (hP : IncreasingProperty P)
    (hQ : IncreasingProperty Q) :
    IncreasingProperty fun G => P G /\ Q G := by
  intro G H hGH h
  exact ⟨hP G H hGH h.1, hQ G H hGH h.2⟩

/-- The native Mathlib formulation of the paper's property `PM`. -/
def HasPerfectMatching (G : SimpleGraph V) : Prop :=
  Exists fun M : G.Subgraph => M.IsPerfectMatching

/-- Perfect-matching existence is an increasing graph property. -/
theorem hasPerfectMatching_mono {G H : SimpleGraph V} (hGH : G <= H) :
    HasPerfectMatching G -> HasPerfectMatching H := by
  rintro ⟨M, hM⟩
  let M' := M.map (SimpleGraph.Hom.ofLE hGH)
  refine ⟨M', ?_⟩
  refine ⟨hM.1.map_ofLE hGH, ?_⟩
  intro v
  simpa [M', SimpleGraph.Subgraph.map_verts,
    SimpleGraph.Hom.coe_ofLE] using hM.2 v

theorem hasPerfectMatching_increasing :
    IncreasingProperty (HasPerfectMatching : SimpleGraph V -> Prop) := by
  intro G H hGH
  exact hasPerfectMatching_mono hGH

/-- Probability of achieving a graph property under a law on realized plays. -/
def successProbability {T : Nat}
    (law : Measure (Play V T)) (property : SimpleGraph V -> Prop) : Real :=
  law.real {play | property play.graph}

/-! ## The property `PM` with the paper's convention for odd `n` -/

/-- The paper's property `PM`: a matching saturating all but at most one vertex (Section 1.2).
On an even number of vertices this is a perfect matching. -/
def HasNearPerfectMatching (G : SimpleGraph V) : Prop :=
  ∃ M : G.Subgraph, M.IsMatching ∧ (M.vertsᶜ).ncard ≤ 1

/-- A perfect matching is in particular a near-perfect one. -/
theorem HasPerfectMatching.hasNearPerfectMatching {G : SimpleGraph V}
    (h : HasPerfectMatching G) : HasNearPerfectMatching G := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, hM.1, ?_⟩
  rw [SimpleGraph.Subgraph.isSpanning_iff.mp hM.2, Set.compl_univ, Set.ncard_empty]
  exact zero_le_one

/-- Near-perfect matchings are preserved by adding edges. -/
theorem hasNearPerfectMatching_mono {G H : SimpleGraph V} (hGH : G ≤ H) :
    HasNearPerfectMatching G → HasNearPerfectMatching H := by
  rintro ⟨M, hM, hcard⟩
  refine ⟨M.map (SimpleGraph.Hom.ofLE hGH), hM.map_ofLE hGH, ?_⟩
  simpa [SimpleGraph.Subgraph.map_verts, SimpleGraph.Hom.coe_ofLE] using hcard

theorem hasNearPerfectMatching_increasing :
    IncreasingProperty (HasNearPerfectMatching : SimpleGraph V → Prop) :=
  fun _ _ hGH h => hasNearPerfectMatching_mono hGH h

/-! ## Histories, strategies and the generated graph (Section 1.1) -/

open Filter Topology
open scoped ENNReal NNReal

/-- The history of a play: the pairs `(u_i, v_i)` of square and circle, in chronological
order. -/
abbrev History (V : Type*) := List (V × V)

/-- A strategy of the paper: for the history `(u_1, v_1, …, u_{t-1}, v_{t-1})` and the square
`u_t` it prescribes the distribution `f_t(u_1, v_1, …, u_{t-1}, v_{t-1}, u_t)` from which the
circle `v_t` is drawn. -/
abbrev Strategy (V : Type*) := History V → V → PMF V

/-- A strategy answering deterministically (an atomic distribution `f_t`). -/
abbrev DeterministicStrategy (V : Type*) := History V → V → V

/-- Every deterministic strategy is a strategy. -/
def liftDeterministic (strategy : DeterministicStrategy V) : Strategy V :=
  fun history offered => PMF.pure (strategy history offered)

/-- The underlying simple graph of a history: loops and repeated edges are discarded, as in
the paper's passage from the multigraph `G_t` to the graph in which a perfect matching is
sought. -/
def historyGraph : History V → SimpleGraph V
  | [] => ⊥
  | (offered, response) :: history => addEdge (historyGraph history) offered response

theorem historyGraph_nil : historyGraph ([] : History V) = ⊥ :=
  rfl

theorem historyGraph_cons (u v : V) (history : History V) :
    historyGraph ((u, v) :: history) = addEdge (historyGraph history) u v :=
  rfl

theorem historyGraph_append (h₁ h₂ : History V) :
    historyGraph (h₁ ++ h₂) = historyGraph h₁ ⊔ historyGraph h₂ := by
  induction h₁ with
  | nil => rw [List.nil_append, historyGraph_nil, bot_sup_eq]
  | cons e h ih =>
      obtain ⟨u, v⟩ := e
      simp only [List.cons_append, historyGraph_cons, ih, addEdge]
      exact sup_right_comm _ _ _

/-- Later rounds only add edges. -/
theorem historyGraph_le_append (h₁ h₂ : History V) :
    historyGraph h₁ ≤ historyGraph (h₁ ++ h₂) := by
  rw [historyGraph_append]
  exact le_sup_left

/-! ## The law of the semi-random process -/

section Process

variable [Fintype V] [Nonempty V]

/-- One round of the process from the history `history`: the square is uniform on the vertex
set, the circle is drawn from the strategy, and the pair is appended to the history. -/
def step (S : Strategy V) (history : History V) : PMF (History V) :=
  (PMF.uniformOfFintype V).bind fun offered =>
    (S history offered).bind fun response => PMF.pure (history ++ [(offered, response)])

theorem exists_of_mem_support_step {S : Strategy V} {history h : History V}
    (hh : h ∈ (step S history).support) :
    ∃ offered response, h = history ++ [(offered, response)] := by
  simp only [step, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hh
  obtain ⟨offered, -, response, -, rfl⟩ := hh
  exact ⟨offered, response, rfl⟩

/-- The law of the history after `t` rounds of the process started from the history `h₀`. -/
def playLawFrom (S : Strategy V) (h₀ : History V) : ℕ → PMF (History V)
  | 0 => PMF.pure h₀
  | t + 1 => (playLawFrom S h₀ t).bind (step S)

/-- The law of the history after `t` rounds of the process started from the empty graph. -/
def playLaw (S : Strategy V) (t : ℕ) : PMF (History V) :=
  playLawFrom S [] t

theorem playLawFrom_zero (S : Strategy V) (h₀ : History V) :
    playLawFrom S h₀ 0 = PMF.pure h₀ :=
  rfl

theorem playLawFrom_succ (S : Strategy V) (h₀ : History V) (t : ℕ) :
    playLawFrom S h₀ (t + 1) = (playLawFrom S h₀ t).bind (step S) :=
  rfl

/-- The Markov property: `t₁ + t₂` rounds are `t₁` rounds followed by `t₂` rounds from the
history reached. -/
theorem playLawFrom_add (S : Strategy V) (h₀ : History V) (t₁ t₂ : ℕ) :
    playLawFrom S h₀ (t₁ + t₂) = (playLawFrom S h₀ t₁).bind fun h => playLawFrom S h t₂ := by
  induction t₂ with
  | zero => exact (PMF.bind_pure _).symm
  | succ t ih =>
      calc playLawFrom S h₀ (t₁ + (t + 1))
          = (playLawFrom S h₀ (t₁ + t)).bind (step S) := rfl
        _ = ((playLawFrom S h₀ t₁).bind fun h => playLawFrom S h t).bind (step S) := by rw [ih]
        _ = (playLawFrom S h₀ t₁).bind fun h => playLawFrom S h (t + 1) := PMF.bind_bind _ _ _

theorem length_of_mem_support_playLawFrom (S : Strategy V) (h₀ : History V) :
    ∀ (t : ℕ) (h : History V), h ∈ (playLawFrom S h₀ t).support → h.length = h₀.length + t
  | 0, h, hh => by
      rw [playLawFrom_zero, PMF.mem_support_pure_iff] at hh
      subst hh
      rfl
  | t + 1, h, hh => by
      rw [playLawFrom_succ, PMF.mem_support_bind_iff] at hh
      obtain ⟨h', hh', hstep⟩ := hh
      obtain ⟨u, v, rfl⟩ := exists_of_mem_support_step hstep
      rw [List.length_append, List.length_singleton,
        length_of_mem_support_playLawFrom S h₀ t h' hh']
      omega

theorem prefix_of_mem_support_playLawFrom (S : Strategy V) (h₀ : History V) :
    ∀ (t : ℕ) (h : History V), h ∈ (playLawFrom S h₀ t).support → h₀ <+: h
  | 0, h, hh => by
      rw [playLawFrom_zero, PMF.mem_support_pure_iff] at hh
      subst hh
      exact List.prefix_rfl
  | t + 1, h, hh => by
      rw [playLawFrom_succ, PMF.mem_support_bind_iff] at hh
      obtain ⟨h', hh', hstep⟩ := hh
      obtain ⟨u, v, rfl⟩ := exists_of_mem_support_step hstep
      exact (prefix_of_mem_support_playLawFrom S h₀ t h' hh').trans (List.prefix_append h' _)

/-! ## Success probabilities -/

/-- `P[G_t ∈ P]` for the process started from the history `h₀`. -/
def successProbFrom (S : Strategy V) (h₀ : History V) (P : SimpleGraph V → Prop) (t : ℕ) :
    ℝ≥0∞ :=
  (playLawFrom S h₀ t).toOuterMeasure {h | P (historyGraph h)}

/-- `P[G_t ∈ P]` for the process started from the empty graph. -/
def successProb (S : Strategy V) (P : SimpleGraph V → Prop) (t : ℕ) : ℝ≥0∞ :=
  successProbFrom S [] P t

theorem successProbFrom_le_one (S : Strategy V) (h₀ : History V) (P : SimpleGraph V → Prop)
    (t : ℕ) : successProbFrom S h₀ P t ≤ 1 := by
  unfold successProbFrom
  calc (playLawFrom S h₀ t).toOuterMeasure {h | P (historyGraph h)}
      ≤ (playLawFrom S h₀ t).toOuterMeasure Set.univ :=
        (playLawFrom S h₀ t).toOuterMeasure_mono fun x _ => Set.mem_univ x
    _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)

theorem successProb_le_one (S : Strategy V) (P : SimpleGraph V → Prop) (t : ℕ) :
    successProb S P t ≤ 1 :=
  successProbFrom_le_one S [] P t

/-- For an increasing property, one more round can only help. -/
theorem successProbFrom_le_succ (S : Strategy V) (h₀ : History V) {P : SimpleGraph V → Prop}
    (hP : IncreasingProperty P) (t : ℕ) :
    successProbFrom S h₀ P t ≤ successProbFrom S h₀ P (t + 1) := by
  unfold successProbFrom
  rw [playLawFrom_succ, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun h => ?_
  by_cases hh : h ∈ {h : History V | P (historyGraph h)}
  · rw [Set.indicator_of_mem hh]
    have hone : (step S h).toOuterMeasure {h : History V | P (historyGraph h)} = 1 := by
      rw [PMF.toOuterMeasure_apply_eq_one_iff]
      intro h' hh'
      obtain ⟨u, v, rfl⟩ := exists_of_mem_support_step hh'
      exact hP _ _ (historyGraph_le_append h _) hh
    rw [hone, mul_one]
  · rw [Set.indicator_of_notMem hh]
    exact zero_le

theorem successProbFrom_mono (S : Strategy V) (h₀ : History V) {P : SimpleGraph V → Prop}
    (hP : IncreasingProperty P) : Monotone (successProbFrom S h₀ P) :=
  monotone_nat_of_le_succ (successProbFrom_le_succ S h₀ hP)

theorem successProb_mono (S : Strategy V) {P : SimpleGraph V → Prop}
    (hP : IncreasingProperty P) : Monotone (successProb S P) :=
  successProbFrom_mono S [] hP

/-! ## The hitting times `τ_P(S, q, n)` and `τ_P(q, n)` -/

/-- `τ_P(S, q, n)`: the least round `t` with `P[G_t ∈ P] ≥ q`, and `∞` if there is none. -/
def hittingTime (S : Strategy V) (P : SimpleGraph V → Prop) (q : ℝ≥0∞) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : q ≤ successProb S P t), (t : ℕ∞)

theorem hittingTime_le {S : Strategy V} {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {t : ℕ}
    (h : q ≤ successProb S P t) : hittingTime S P q ≤ t := by
  unfold hittingTime
  exact iInf₂_le t h

theorem le_hittingTime {S : Strategy V} {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {m : ℕ}
    (h : ∀ t : ℕ, q ≤ successProb S P t → m ≤ t) : (m : ℕ∞) ≤ hittingTime S P q := by
  unfold hittingTime
  exact le_iInf₂ fun t ht => ENat.coe_le_coe.mpr (h t ht)

/-- `τ_P(S, q, n)` is non-decreasing in `q`. -/
theorem hittingTime_mono (S : Strategy V) (P : SimpleGraph V → Prop) :
    Monotone (hittingTime S P) := by
  intro q₁ q₂ hq
  unfold hittingTime
  exact iInf_mono fun _ => iInf_mono' fun h => ⟨hq.trans h, le_rfl⟩

variable (V) in
/-- `τ_P(q, n) = inf_S τ_P(S, q, n)`, the infimum over all strategies on the vertex set. -/
def minHittingTime (P : SimpleGraph V → Prop) (q : ℝ≥0∞) : ℕ∞ :=
  ⨅ S : Strategy V, hittingTime S P q

theorem minHittingTime_le (P : SimpleGraph V → Prop) (q : ℝ≥0∞) (S : Strategy V) :
    minHittingTime V P q ≤ hittingTime S P q :=
  iInf_le _ S

theorem le_minHittingTime {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {m : ℕ∞}
    (h : ∀ S : Strategy V, m ≤ hittingTime S P q) : m ≤ minHittingTime V P q :=
  le_iInf h

/-- `τ_P(q, n)` is non-decreasing in `q`, as observed in Section 1.1. -/
theorem minHittingTime_mono (P : SimpleGraph V → Prop) : Monotone (minHittingTime V P) :=
  fun _ _ hq => iInf_mono fun S => hittingTime_mono S P hq

end Process

/-! ## The constant `τ_P` -/

/-- `limsup_{n → ∞} τ_P(q, n) / n`, over the vertex sets `[n] = Fin n`, `n ≥ 1`
(the index `n` of the `limsup` below is the paper's `n - 1`). -/
def tauAt (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (q : ℝ≥0∞) : ℝ≥0∞ :=
  limsup (fun n : ℕ =>
    ((minHittingTime (Fin (n + 1)) (P (n + 1)) q : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞)) atTop

/-- `τ_P = lim_{q → 1⁻} limsup_{n → ∞} τ_P(q, n) / n`.  The function of `q` is non-decreasing,
so the left limit is the supremum over `0 < q < 1`; `tendsto_tauAt` below confirms that this
is the paper's limit. -/
def tau (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : ℝ≥0∞ :=
  ⨆ q ∈ Set.Ioo (0 : ℝ≥0∞) 1, tauAt P q

theorem tauAt_mono (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Monotone (tauAt P) := by
  intro q₁ q₂ hq
  unfold tauAt
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  exact ENNReal.div_le_div_right (ENat.toENNReal_mono (minHittingTime_mono _ hq)) _

theorem tauAt_le_tau (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) {q : ℝ≥0∞}
    (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1) : tauAt P q ≤ tau P := by
  unfold tau
  exact le_iSup₂ (f := fun q _ => tauAt P q) q hq

/-- `τ_P` is the left limit at `q = 1` of `q ↦ limsup_n τ_P(q, n) / n`, as in the paper. -/
theorem tendsto_tauAt (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) :
    Tendsto (tauAt P) (𝓝[<] 1) (𝓝 (tau P)) := by
  have h := (tauAt_mono P).tendsto_nhdsLT 1
  convert h using 2
  apply le_antisymm
  · exact iSup₂_le fun q hq => le_sSup ⟨q, hq.2, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨q, hq, rfl⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ q) with hq0 | hq0
    · subst hq0
      calc tauAt P 0 ≤ tauAt P (1 / 2) := tauAt_mono P zero_le
        _ ≤ tau P :=
          tauAt_le_tau P ⟨ENNReal.half_pos one_ne_zero,
            ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top⟩
    · exact tauAt_le_tau P ⟨hq0, hq⟩

/-! ## From almost-sure statements to bounds on `τ_P` -/

/-- **Upper bounds on `τ_P` from a.a.s. statements.**  If for every `ε > 0` there are
strategies `S_n` such that `P` holds after `⌈(α + ε) n⌉` rounds with probability tending to
`1`, then `τ_P ≤ α`.  This is how the paper passes from Proposition 2.3 and the clean-up
algorithm to Theorem 1.1. -/
theorem tau_le_of_forall_exists_tendsto (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) {α : ℝ}
    (hα : 0 ≤ α)
    (h : ∀ ε : ℝ, 0 < ε → ∃ S : ∀ n : ℕ, Strategy (Fin (n + 1)),
      Tendsto (fun n : ℕ => successProb (S n) (P (n + 1)) ⌈(α + ε) * ((n + 1 : ℕ) : ℝ)⌉₊)
        atTop (𝓝 1)) :
    tau P ≤ ENNReal.ofReal α := by
  unfold tau
  refine iSup₂_le fun q hq => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
  obtain ⟨S, hS⟩ := h ((ε : ℝ) / 2) hε2
  have hev : ∀ᶠ n : ℕ in atTop,
      q < successProb (S n) (P (n + 1)) ⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ :=
    (tendsto_order.1 hS).1 q hq.2
  have hlin : Tendsto (fun n : ℕ => (ε : ℝ) / 2 * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε2 (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hev2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (ε : ℝ) / 2 * ((n + 1 : ℕ) : ℝ) :=
    hlin.eventually_ge_atTop 1
  unfold tauAt
  refine limsup_le_of_le (h := ?_)
  filter_upwards [hev, hev2] with n hn1 hn2
  have hm : ((minHittingTime (Fin (n + 1)) (P (n + 1)) q : ℕ∞) : ℝ≥0∞)
      ≤ ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) := by
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.mpr
      ((minHittingTime_le _ _ (S n)).trans (hittingTime_le hn1.le))
  have hreal : ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
      ≤ (α + (ε : ℝ)) * ((n + 1 : ℕ) : ℝ) := by
    have h1 := Nat.ceil_lt_add_one
      (mul_nonneg (add_nonneg hα hε2.le) (Nat.cast_nonneg (n + 1)) :
        (0 : ℝ) ≤ (α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ))
    have h2 : (α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ) + (ε : ℝ) / 2 * ((n + 1 : ℕ) : ℝ)
        = (α + (ε : ℝ)) * ((n + 1 : ℕ) : ℝ) := by ring
    linarith
  have hT : ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞)
      ≤ (ENNReal.ofReal α + ε) * ((n + 1 : ℕ) : ℝ≥0∞) := by
    calc ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal ((α + (ε : ℝ)) * ((n + 1 : ℕ) : ℝ)) := ENNReal.ofReal_le_ofReal hreal
      _ = (ENNReal.ofReal α + ε) * ((n + 1 : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.ofReal_mul (add_nonneg hα ε.coe_nonneg), ENNReal.ofReal_add hα ε.coe_nonneg,
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  calc ((minHittingTime (Fin (n + 1)) (P (n + 1)) q : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞)
      ≤ ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right hm _
    _ ≤ ENNReal.ofReal α + ε :=
        (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr n.succ_ne_zero)
          (ENNReal.natCast_ne_top _)).mpr hT

/-- **Lower bounds on `τ_P` from a.a.s. statements** (Proposition 3.1 of the paper).  If for
some `0 < q < 1` and every `ε > 0`, eventually no strategy achieves `P` with probability `q`
within `(β - ε) n` rounds, then `τ_P ≥ β`. -/
theorem le_tau_of_forall_eventually (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) {β : ℝ}
    {q : ℝ≥0∞} (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Strategy (Fin (n + 1)), ∀ t : ℕ,
      (t : ℝ) ≤ (β - ε) * ((n + 1 : ℕ) : ℝ) → successProb S (P (n + 1)) t < q) :
    ENNReal.ofReal β ≤ tau P := by
  refine le_trans ?_ (tauAt_le_tau P hq)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have key : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (β - ε) ≤
      ((minHittingTime (Fin (n + 1)) (P (n + 1)) q : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) := by
    filter_upwards [h ε (NNReal.coe_pos.mpr hε)] with n hn
    have hle : ((⌈(β - (ε : ℝ)) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℕ∞)
        ≤ minHittingTime (Fin (n + 1)) (P (n + 1)) q := by
      refine le_minHittingTime fun S => le_hittingTime fun t ht => ?_
      by_contra hcon
      have hlt : (t : ℝ) < (β - (ε : ℝ)) * ((n + 1 : ℕ) : ℝ) :=
        Nat.lt_ceil.mp (not_le.mp hcon)
      exact absurd ht (not_le.mpr (hn S t hlt.le))
    rw [ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr n.succ_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))]
    calc ENNReal.ofReal (β - ε) * ((n + 1 : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal ((β - (ε : ℝ)) * ((n + 1 : ℕ) : ℝ)) := by
          rw [ENNReal.ofReal_mul' (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ((⌈(β - (ε : ℝ)) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ ((minHittingTime (Fin (n + 1)) (P (n + 1)) q : ℕ∞) : ℝ≥0∞) := by
          rw [← ENat.toENNReal_coe]
          exact ENat.toENNReal_le.mpr hle
  have hlim : ENNReal.ofReal (β - ε) ≤ tauAt P q :=
    le_limsup_of_le (h := fun b hb => by
      obtain ⟨n, hn1, hn2⟩ := (key.and hb).exists
      exact hn1.trans hn2)
  calc ENNReal.ofReal β = ENNReal.ofReal ((β - ε) + ε) := by rw [sub_add_cancel]
    _ ≤ ENNReal.ofReal (β - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (β - ε) + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ tauAt P q + ε := add_le_add hlim le_rfl

/-- For an increasing property it suffices to look at the single round `⌊(β - ε) n⌋`. -/
theorem le_tau_of_forall_eventually_of_increasing (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop)
    (hP : ∀ n, IncreasingProperty (P n)) {β : ℝ} {q : ℝ≥0∞} (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Strategy (Fin (n + 1)),
      successProb S (P (n + 1)) ⌊(β - ε) * ((n + 1 : ℕ) : ℝ)⌋₊ < q) :
    ENNReal.ofReal β ≤ tau P := by
  refine le_tau_of_forall_eventually P hq fun ε hε => ?_
  filter_upwards [h ε hε] with n hn S t ht
  exact lt_of_le_of_lt (successProb_mono S (hP (n + 1)) (Nat.le_floor ht)) (hn S)

/-! ## The property `PM` on the vertex sets `[n]` -/

/-- The property `PM` on the vertex set `[n]`, with the paper's convention for odd `n`. -/
def perfectMatchingProperty : ∀ n : ℕ, SimpleGraph (Fin n) → Prop :=
  fun _ G => HasNearPerfectMatching G

theorem perfectMatchingProperty_increasing (n : ℕ) :
    IncreasingProperty (perfectMatchingProperty n) :=
  hasNearPerfectMatching_increasing

/-- Decimal literals of `ℝ≥0∞` are the images of the corresponding real literals. -/
theorem ofReal_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ENNReal.ofReal (OfScientific.ofScientific m s e : ℝ) =
      (OfScientific.ofScientific m s e : ℝ≥0∞) := by
  rw [← NNReal.coe_ofScientific, ENNReal.ofReal_coe_nnreal]
  rfl

/-! ## The main theorem -/

/-- **Theorem 1.1** (Gao, MacRury, Prałat).  `τ_PM ≤ β + 10⁻⁵ ≤ 1.20524`: for every `q < 1` and
`ε > 0`, for all large `n` some strategy builds a perfect matching on `[n]` (all but one
vertex saturated when `n` is odd) with probability at least `q` within `(1.20524 + ε) n`
rounds of the semi-random graph process.  The paper's `β` is derived from the differential
equations of the `1100`-phase algorithm of Section 2.2 (Proposition 2.3: `1.20365 n` rounds
to saturate all but `10⁻⁶ n` vertices), followed by the randomised algorithm of Section 2.1
and the clean-up (`0.00158 n + 10⁻⁵ n` rounds). -/
theorem P105 : tau perfectMatchingProperty ≤ 1.20524 := by
  sorry

/-! ## Direct corollaries -/

/-- `τ_PM` is finite. -/
theorem tau_perfectMatching_ne_top : tau perfectMatchingProperty ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [← ofReal_ofScientific]; exact ENNReal.ofReal_ne_top)
    P105

/-- Theorem 1.1 improves the previously best upper bound `1 + 2/e < 1.73576` of Ben-Eliezer,
Hefetz, Kronenberg, Parczyk, Shikhelman and Stojaković (reference [3] of the paper), obtained
by coupling with the bipartite `1`-out process. -/
theorem tau_perfectMatching_lt_previous_bound : tau perfectMatchingProperty < 1.73576 :=
  lt_of_le_of_lt P105 (by
    rw [← ofReal_ofScientific, ← ofReal_ofScientific,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num)

/-- A perfect matching is built in fewer than `2n` rounds. -/
theorem tau_perfectMatching_lt_two : tau perfectMatchingProperty < 2 :=
  lt_of_le_of_lt P105 (by
    rw [← ofReal_ofScientific, ← ENNReal.ofReal_ofNat 2,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num)

end PerfectMatchingSemiRandom
