import ProofBench.PROBLEMS.P105.P105
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.ENNReal.Lemmas

/- ---------------------------------------------------- -/
/- Paper: On the pre- and post-positional semi-random graph processes -/
/- ---------------------------------------------------- -/

/-!
# P049: On the pre- and post-positional semi-random graph processes

This file formalizes the two semi-random graph processes of Section 1.1 and
the main theorem of

  P. Gao and H. Koerts, *On the pre- and post-positional semi-random graph
  processes*, arXiv:2309.05881.

## The paper's dependency graph

* Section 1.1 and Section 2: the *post-positional* process (the original
  process of Ben-Eliezer, Hefetz, Kronenberg, Parczyk, Shikhelman and
  Stojaković): in round `t` a square `u_t` is chosen uniformly at random and
  the player answers with a circle `v_t`, which may depend on `u_t`; the
  *pre-positional* process (proposed by Wormald): the player chooses `v_t`
  first and `u_t` is then uniform, independent of `v_t`.  Loops and multiple
  edges may arise; all properties concern the underlying simple graph.
  A property is *increasing* if it is preserved by adding edges.
* Section 3, **Lemma 3.1**: the post-positional process constructs a graph in
  `P` at least as fast as the pre-positional one, by the samplewise coupling
  in which the post-positional player copies the pre-positional choices.
* Section 4, `k`-connectivity: `α_1 = 1` (Lemma 4.2) and, for `k ≥ 2`, `α_k`
  is the constant of Wormald's min-degree process, `α_2 = ln 2 + ln(1 + ln 2)`
  (Lemma 4.3, Propositions 4.9-4.12, Lemma 4.13) and `α_k` for `k ≥ 3` from
  Ben-Eliezer et al. (Lemma 4.1).  Section 4.2 introduces the constant
  `τ_P = lim_{q ↑ 1} limsup_n τ_P(q, n) / n`.
* **Theorem 1.1**, the main theorem: for every fixed `k ≥ 1` there is a real
  number `α_k` such that for every `ε > 0`, a.a.s. (a) no strategy in either
  process constructs a `k`-connected graph in at most `(α_k - ε) n` rounds,
  and (b) both processes have strategies constructing a `k`-connected graph in
  at most `(α_k + ε) n` rounds.  It settles the open case `k = 2` of the
  original process (Remark 1.2).
* Theorems 1.4 (`d`-degenerate subgraphs, Section 5), 1.6 (dense bipartite
  subgraphs, Section 6) and 1.8 (induced `(n-1)`-cycles, Section 7) are the
  other results of the paper.

## What is formalized here

The target of the problem is **Theorem 1.1**, stated at the end of this file as
`P106` and proved by `sorry`, the single `sorry` of the file.
Everything else is proved from first principles with no `sorry` and no new
axiom:

* `History`, `PreStrategy`, `PostStrategy`, `liftPre`, `runPreFrom`,
  `runPostFrom`, `historyGraph`: histories `(u_1, v_1, …, u_t, v_t)`,
  deterministic strategies, and the samplewise coupling of Lemma 3.1
  (`runPostFrom_liftPre_eq_runPreFrom`);
* `PreRandomStrategy`, `PostRandomStrategy`: randomized strategies, as
  distributions on the vertex set depending on the history (and, for the
  post-positional process, on the current square);
* `stepPost`, `stepPre`, `playLawFrom`, `playLaw`, `successProb`: the laws of
  the two processes, built round by round, and `P[G_t ∈ P]`;
* `stepPost_liftPreRandom`, `tau_post_le_pre`: **Lemma 3.1** in law form: the
  post-positional process playing a pre-positional strategy has exactly the
  law of the pre-positional process, hence `τ_P^{post} ≤ τ_P^{pre}` for every
  property `P`;
* `ProcessFamily`, `tau`: the constant `τ_P` of Section 4.2 for a family of
  processes, with the bridge lemmas from a.a.s. statements to bounds on `τ_P`;
* `IsKConnected`, `kConnectedProperty`: `k`-connectivity as defined in
  Section 4 (connected, and still connected after removing fewer than `k`
  vertices), an increasing property.

## What is deliberately not asserted

* The constants `α_k` are only characterised through the min-degree process
  (Remark 1.2(c)); the theorem asserts their existence, as the paper does.
* Theorems 1.4, 1.6 and 1.8 and Lemmas 4.1-4.3 are not stated, since the file
  carries a single `sorry`.
* Nothing about the explicit strategies of Sections 4-7 is encoded.

## Conventions

* Vertex sets are `Fin (n + 1)`, i.e. `[n]` for `n ≥ 1`.  "In at most `T`
  rounds" is read at round `T`: since `k`-connectivity is increasing, the
  graph after `⌊T⌋` rounds is `k`-connected iff some earlier graph is.
* Probabilities live in `ℝ≥0∞` and hitting times in `ℕ∞`, as in Section 4.2.
* Theorem 1.1(a) is read as "for every sequence of strategies, the probability
  of success within `(α_k - ε) n` rounds tends to `0`"; Theorem 1.1(b) as the
  existence of a sequence of strategies whose probability of success within
  `(α_k + ε) n` rounds tends to `1`.
-/

noncomputable section

namespace PositionalSemiRandom

open PerfectMatchingSemiRandom Filter Topology
open scoped ENNReal NNReal

variable {V : Type*}

/-! ## Histories and deterministic strategies (Section 2, Lemma 3.1) -/

/-- The ordered list of offered/response pairs already played. -/
abbrev History (V : Type*) := List (V × V)

/-- A deterministic pre-positional strategy cannot inspect the current
uniformly random offered vertex. -/
abbrev PreStrategy (V : Type*) := History V → V

/-- A deterministic post-positional strategy sees the current offered vertex
before selecting its response. -/
abbrev PostStrategy (V : Type*) := History V → V → V

/-- Regard a pre-positional strategy as a post-positional one by ignoring the
newly offered vertex. -/
def liftPre (strategy : PreStrategy V) : PostStrategy V :=
  fun history _offered => strategy history

@[simp]
theorem liftPre_apply (strategy : PreStrategy V) (history : History V)
    (offered : V) :
    liftPre strategy history offered = strategy history :=
  rfl

/-- Execute a pre-positional strategy against a fixed sequence of random
offers, beginning from an existing history. -/
def runPreFrom (strategy : PreStrategy V) :
    History V → List V → History V
  | history, [] => history
  | history, offered :: offers =>
      let response := strategy history
      runPreFrom strategy (history ++ [(offered, response)]) offers

/-- Execute a post-positional strategy against a fixed offer sequence. -/
def runPostFrom (strategy : PostStrategy V) :
    History V → List V → History V
  | history, [] => history
  | history, offered :: offers =>
      let response := strategy history offered
      runPostFrom strategy (history ++ [(offered, response)]) offers

/-- The samplewise coupling in Lemma 3.1: the lifted post-positional strategy
produces exactly the same history as the original pre-positional strategy for
every realization of the random offers. -/
theorem runPostFrom_liftPre_eq_runPreFrom
    (strategy : PreStrategy V) (history : History V) (offers : List V) :
    runPostFrom (liftPre strategy) history offers =
      runPreFrom strategy history offers := by
  induction offers generalizing history with
  | nil => rfl
  | cons offered offers ih =>
      simp only [runPostFrom, runPreFrom, liftPre]
      exact ih _

/-- Convert a play history to its underlying simple graph: loops and multiple edges are
discarded, as in Section 2. -/
def historyGraph : History V → SimpleGraph V
  | [] => ⊥
  | (offered, response) :: history =>
      addEdge (historyGraph history) offered response

/-- Consequently, the coupled pre- and post-positional processes have the
same underlying simple graph on every offer sequence. -/
theorem historyGraph_runPostFrom_liftPre
    (strategy : PreStrategy V) (history : History V) (offers : List V) :
    historyGraph (runPostFrom (liftPre strategy) history offers) =
      historyGraph (runPreFrom strategy history offers) := by
  rw [runPostFrom_liftPre_eq_runPreFrom]

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

/-! ## Randomized strategies -/

/-- A randomized pre-positional strategy: the distribution of the circle `v_t`, which may
depend on the history but not on the square `u_t`, drawn afterwards. -/
abbrev PreRandomStrategy (V : Type*) := History V → PMF V

/-- A randomized post-positional strategy: the distribution of the circle `v_t`, which may
depend on the history and on the square `u_t`. -/
abbrev PostRandomStrategy (V : Type*) := History V → V → PMF V

/-- A deterministic pre-positional strategy as a randomized one. -/
def PreStrategy.toRandom (strategy : PreStrategy V) : PreRandomStrategy V :=
  fun history => PMF.pure (strategy history)

/-- A deterministic post-positional strategy as a randomized one. -/
def PostStrategy.toRandom (strategy : PostStrategy V) : PostRandomStrategy V :=
  fun history offered => PMF.pure (strategy history offered)

/-- The post-positional strategy copying the choices of a pre-positional one (Lemma 3.1). -/
def liftPreRandom (strategy : PreRandomStrategy V) : PostRandomStrategy V :=
  fun history _offered => strategy history

theorem liftPreRandom_toRandom (strategy : PreStrategy V) :
    liftPreRandom strategy.toRandom = (liftPre strategy).toRandom :=
  rfl

/-! ## The laws of the two processes -/

/-- A one-round kernel which appends exactly one pair to the history. -/
def IsAppendStep (step : History V → PMF (History V)) : Prop :=
  ∀ history h, h ∈ (step history).support → ∃ u v, h = history ++ [(u, v)]

section Kernels

variable [Fintype V] [Nonempty V]

/-- One round of the post-positional process from the history `history`: the square is
uniform, the circle is drawn from the strategy given the square, and the pair is appended. -/
def stepPost (S : PostRandomStrategy V) (history : History V) : PMF (History V) :=
  (PMF.uniformOfFintype V).bind fun offered =>
    (S history offered).bind fun response => PMF.pure (history ++ [(offered, response)])

/-- One round of the pre-positional process: the circle is drawn first from the strategy, the
square is uniform and independent of it, and the pair is appended. -/
def stepPre (S : PreRandomStrategy V) (history : History V) : PMF (History V) :=
  (S history).bind fun response =>
    (PMF.uniformOfFintype V).bind fun offered => PMF.pure (history ++ [(offered, response)])

/-- **Lemma 3.1 in law form, one round**: the post-positional process playing the copy of a
pre-positional strategy has the law of the pre-positional process. -/
theorem stepPost_liftPreRandom (S : PreRandomStrategy V) :
    stepPost (liftPreRandom S) = stepPre S := by
  funext history
  unfold stepPost stepPre liftPreRandom
  exact PMF.bind_comm (PMF.uniformOfFintype V) (S history)
    fun offered response => PMF.pure (history ++ [(offered, response)])

theorem isAppendStep_stepPost (S : PostRandomStrategy V) : IsAppendStep (stepPost S) := by
  intro history h hh
  simp only [stepPost, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hh
  obtain ⟨u, -, v, -, rfl⟩ := hh
  exact ⟨u, v, rfl⟩

theorem isAppendStep_stepPre (S : PreRandomStrategy V) : IsAppendStep (stepPre S) := by
  intro history h hh
  simp only [stepPre, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hh
  obtain ⟨v, -, u, -, rfl⟩ := hh
  exact ⟨u, v, rfl⟩

end Kernels

section Process

variable (step : History V → PMF (History V))

/-- The law of the history after `t` rounds of the process with one-round kernel `step`,
started from the history `h₀`. -/
def playLawFrom (h₀ : History V) : ℕ → PMF (History V)
  | 0 => PMF.pure h₀
  | t + 1 => (playLawFrom h₀ t).bind step

/-- The law of the history after `t` rounds, started from the empty graph. -/
def playLaw (t : ℕ) : PMF (History V) :=
  playLawFrom step [] t

theorem playLawFrom_zero (h₀ : History V) : playLawFrom step h₀ 0 = PMF.pure h₀ :=
  rfl

theorem playLawFrom_succ (h₀ : History V) (t : ℕ) :
    playLawFrom step h₀ (t + 1) = (playLawFrom step h₀ t).bind step :=
  rfl

/-- The Markov property of the process. -/
theorem playLawFrom_add (h₀ : History V) (t₁ t₂ : ℕ) :
    playLawFrom step h₀ (t₁ + t₂) =
      (playLawFrom step h₀ t₁).bind fun h => playLawFrom step h t₂ := by
  induction t₂ with
  | zero => exact (PMF.bind_pure _).symm
  | succ t ih =>
      calc playLawFrom step h₀ (t₁ + (t + 1))
          = (playLawFrom step h₀ (t₁ + t)).bind step := rfl
        _ = ((playLawFrom step h₀ t₁).bind fun h => playLawFrom step h t).bind step := by
            rw [ih]
        _ = (playLawFrom step h₀ t₁).bind fun h => playLawFrom step h (t + 1) :=
            PMF.bind_bind _ _ _

theorem length_of_mem_support_playLawFrom (hstep : IsAppendStep step) (h₀ : History V) :
    ∀ (t : ℕ) (h : History V), h ∈ (playLawFrom step h₀ t).support → h.length = h₀.length + t
  | 0, h, hh => by
      rw [playLawFrom_zero, PMF.mem_support_pure_iff] at hh
      subst hh
      rfl
  | t + 1, h, hh => by
      rw [playLawFrom_succ, PMF.mem_support_bind_iff] at hh
      obtain ⟨h', hh', hs⟩ := hh
      obtain ⟨u, v, rfl⟩ := hstep h' h hs
      rw [List.length_append, List.length_singleton,
        length_of_mem_support_playLawFrom hstep h₀ t h' hh']
      omega

/-! ### Success probabilities and hitting times (Section 4.2) -/

/-- `P[G_t ∈ P]` for the process started from `h₀`. -/
def successProbFrom (h₀ : History V) (P : SimpleGraph V → Prop) (t : ℕ) : ℝ≥0∞ :=
  (playLawFrom step h₀ t).toOuterMeasure {h | P (historyGraph h)}

/-- `P[G_t ∈ P]` for the process started from the empty graph. -/
def successProb (P : SimpleGraph V → Prop) (t : ℕ) : ℝ≥0∞ :=
  successProbFrom step [] P t

theorem successProbFrom_le_one (h₀ : History V) (P : SimpleGraph V → Prop) (t : ℕ) :
    successProbFrom step h₀ P t ≤ 1 := by
  unfold successProbFrom
  calc (playLawFrom step h₀ t).toOuterMeasure {h | P (historyGraph h)}
      ≤ (playLawFrom step h₀ t).toOuterMeasure Set.univ :=
        (playLawFrom step h₀ t).toOuterMeasure_mono fun x _ => Set.mem_univ x
    _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)

theorem successProb_le_one (P : SimpleGraph V → Prop) (t : ℕ) : successProb step P t ≤ 1 :=
  successProbFrom_le_one step [] P t

/-- At round `0` the graph is empty: a property failing for the empty graph has probability
`0`. -/
theorem successProb_zero_of_not {P : SimpleGraph V → Prop} (hP : ¬ P ⊥) :
    successProb step P 0 = 0 := by
  unfold successProb successProbFrom
  rw [playLawFrom_zero, PMF.toOuterMeasure_pure_apply, if_neg]
  exact hP

/-- For an increasing property, one more round can only help. -/
theorem successProbFrom_le_succ (hstep : IsAppendStep step) (h₀ : History V)
    {P : SimpleGraph V → Prop} (hP : IncreasingProperty P) (t : ℕ) :
    successProbFrom step h₀ P t ≤ successProbFrom step h₀ P (t + 1) := by
  unfold successProbFrom
  rw [playLawFrom_succ, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine ENNReal.tsum_le_tsum fun h => ?_
  by_cases hh : h ∈ {h : History V | P (historyGraph h)}
  · rw [Set.indicator_of_mem hh]
    have hone : (step h).toOuterMeasure {h : History V | P (historyGraph h)} = 1 := by
      rw [PMF.toOuterMeasure_apply_eq_one_iff]
      intro h' hh'
      obtain ⟨u, v, rfl⟩ := hstep h h' hh'
      exact hP _ _ (historyGraph_le_append h _) hh
    rw [hone, mul_one]
  · rw [Set.indicator_of_notMem hh]
    exact zero_le

theorem successProb_mono (hstep : IsAppendStep step) {P : SimpleGraph V → Prop}
    (hP : IncreasingProperty P) : Monotone (successProb step P) :=
  monotone_nat_of_le_succ (successProbFrom_le_succ step hstep [] hP)

/-- `τ_P(S, q, n)`: the least round `t` with `P[G_t ∈ P] ≥ q`, and `∞` if there is none. -/
def hittingTime (P : SimpleGraph V → Prop) (q : ℝ≥0∞) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : q ≤ successProb step P t), (t : ℕ∞)

theorem hittingTime_le {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {t : ℕ}
    (h : q ≤ successProb step P t) : hittingTime step P q ≤ t := by
  unfold hittingTime
  exact iInf₂_le t h

theorem le_hittingTime {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {m : ℕ}
    (h : ∀ t : ℕ, q ≤ successProb step P t → m ≤ t) : (m : ℕ∞) ≤ hittingTime step P q := by
  unfold hittingTime
  exact le_iInf₂ fun t ht => ENat.coe_le_coe.mpr (h t ht)

theorem hittingTime_mono (P : SimpleGraph V → Prop) : Monotone (hittingTime step P) := by
  intro q₁ q₂ hq
  unfold hittingTime
  exact iInf_mono fun _ => iInf_mono' fun h => ⟨hq.trans h, le_rfl⟩

end Process

/-! ## The constant `τ_P` of Section 4.2 for a family of processes -/

/-- A semi-random process on every vertex set `[n]`, `n ≥ 1`: a type of strategies and the
one-round kernel of each strategy. -/
structure ProcessFamily where
  /-- The strategies on the vertex set `Fin (n + 1)`. -/
  Strat : ℕ → Type
  /-- The one-round kernel of a strategy. -/
  step : ∀ n, Strat n → History (Fin (n + 1)) → PMF (History (Fin (n + 1)))

namespace ProcessFamily

variable (F : ProcessFamily)

/-- `τ_P(q, n)`, the infimum over all strategies of `τ_P(S, q, n)`. -/
def minHittingTime (n : ℕ) (P : SimpleGraph (Fin (n + 1)) → Prop) (q : ℝ≥0∞) : ℕ∞ :=
  ⨅ S : F.Strat n, hittingTime (F.step n S) P q

theorem minHittingTime_le (n : ℕ) (P : SimpleGraph (Fin (n + 1)) → Prop) (q : ℝ≥0∞)
    (S : F.Strat n) : F.minHittingTime n P q ≤ hittingTime (F.step n S) P q :=
  iInf_le _ S

theorem le_minHittingTime {n : ℕ} {P : SimpleGraph (Fin (n + 1)) → Prop} {q : ℝ≥0∞}
    {m : ℕ∞} (h : ∀ S : F.Strat n, m ≤ hittingTime (F.step n S) P q) :
    m ≤ F.minHittingTime n P q :=
  le_iInf h

theorem minHittingTime_mono (n : ℕ) (P : SimpleGraph (Fin (n + 1)) → Prop) :
    Monotone (F.minHittingTime n P) :=
  fun _ _ hq => iInf_mono fun S => hittingTime_mono (F.step n S) P hq

/-- `limsup_{n → ∞} τ_P(q, n) / n` (the index `n` below is the paper's `n - 1`). -/
def tauAt (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (q : ℝ≥0∞) : ℝ≥0∞ :=
  limsup (fun n : ℕ =>
    ((F.minHittingTime n (P (n + 1)) q : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞)) atTop

/-- `τ_P = lim_{q ↑ 1} limsup_n τ_P(q, n) / n` of Section 4.2, as the supremum over
`0 < q < 1` of the non-decreasing function `q ↦ limsup_n τ_P(q, n) / n`;
`tendsto_tauAt` confirms that this is the paper's limit. -/
def tau (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : ℝ≥0∞ :=
  ⨆ q ∈ Set.Ioo (0 : ℝ≥0∞) 1, F.tauAt P q

theorem tauAt_mono (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Monotone (F.tauAt P) := by
  intro q₁ q₂ hq
  unfold tauAt
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  exact ENNReal.div_le_div_right (ENat.toENNReal_mono (F.minHittingTime_mono _ _ hq)) _

theorem tauAt_le_tau (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) {q : ℝ≥0∞}
    (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1) : F.tauAt P q ≤ F.tau P := by
  unfold tau
  exact le_iSup₂ (f := fun q _ => F.tauAt P q) q hq

/-- `τ_P` is the left limit at `q = 1`, as in Section 4.2. -/
theorem tendsto_tauAt (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) :
    Tendsto (F.tauAt P) (𝓝[<] 1) (𝓝 (F.tau P)) := by
  have h := (F.tauAt_mono P).tendsto_nhdsLT 1
  convert h using 2
  apply le_antisymm
  · exact iSup₂_le fun q hq => le_sSup ⟨q, hq.2, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨q, hq, rfl⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ q) with hq0 | hq0
    · subst hq0
      calc F.tauAt P 0 ≤ F.tauAt P (1 / 2) := F.tauAt_mono P zero_le
        _ ≤ F.tau P :=
          F.tauAt_le_tau P ⟨ENNReal.half_pos one_ne_zero,
            ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top⟩
    · exact F.tauAt_le_tau P ⟨hq0, hq⟩

/-- **Upper bounds on `τ_P` from a.a.s. statements.**  If for every `ε > 0` there are
strategies `S_n` such that `P` holds after `⌈(α + ε) n⌉` rounds with probability tending to
`1`, then `τ_P ≤ α`. -/
theorem tau_le_of_forall_exists_tendsto (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) {α : ℝ}
    (hα : 0 ≤ α)
    (h : ∀ ε : ℝ, 0 < ε → ∃ S : ∀ n : ℕ, F.Strat n,
      Tendsto (fun n : ℕ =>
        successProb (F.step n (S n)) (P (n + 1)) ⌈(α + ε) * ((n + 1 : ℕ) : ℝ)⌉₊)
        atTop (𝓝 1)) :
    F.tau P ≤ ENNReal.ofReal α := by
  unfold tau
  refine iSup₂_le fun q hq => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
  obtain ⟨S, hS⟩ := h ((ε : ℝ) / 2) hε2
  have hev : ∀ᶠ n : ℕ in atTop,
      q < successProb (F.step n (S n)) (P (n + 1)) ⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ :=
    (tendsto_order.1 hS).1 q hq.2
  have hlin : Tendsto (fun n : ℕ => (ε : ℝ) / 2 * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε2 (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hev2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (ε : ℝ) / 2 * ((n + 1 : ℕ) : ℝ) :=
    hlin.eventually_ge_atTop 1
  unfold tauAt
  refine limsup_le_of_le (h := ?_)
  filter_upwards [hev, hev2] with n hn1 hn2
  have hm : ((F.minHittingTime n (P (n + 1)) q : ℕ∞) : ℝ≥0∞)
      ≤ ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) := by
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.mpr
      ((F.minHittingTime_le n _ _ (S n)).trans (hittingTime_le _ hn1.le))
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
  calc ((F.minHittingTime n (P (n + 1)) q : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞)
      ≤ ((⌈(α + (ε : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right hm _
    _ ≤ ENNReal.ofReal α + ε :=
        (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr n.succ_ne_zero)
          (ENNReal.natCast_ne_top _)).mpr hT

/-- **Lower bounds on `τ_P` from a.a.s. statements.**  If for some `0 < q < 1` and every
`ε > 0`, eventually no strategy achieves `P` with probability `q` within `(β - ε) n` rounds,
then `τ_P ≥ β`. -/
theorem le_tau_of_forall_eventually (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) {β : ℝ}
    {q : ℝ≥0∞} (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : F.Strat n, ∀ t : ℕ,
      (t : ℝ) ≤ (β - ε) * ((n + 1 : ℕ) : ℝ) → successProb (F.step n S) (P (n + 1)) t < q) :
    ENNReal.ofReal β ≤ F.tau P := by
  refine le_trans ?_ (F.tauAt_le_tau P hq)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have key : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (β - ε) ≤
      ((F.minHittingTime n (P (n + 1)) q : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) := by
    filter_upwards [h ε (NNReal.coe_pos.mpr hε)] with n hn
    have hle : ((⌈(β - (ε : ℝ)) * ((n + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℕ∞)
        ≤ F.minHittingTime n (P (n + 1)) q := by
      refine F.le_minHittingTime fun S => le_hittingTime _ fun t ht => ?_
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
      _ ≤ ((F.minHittingTime n (P (n + 1)) q : ℕ∞) : ℝ≥0∞) := by
          rw [← ENat.toENNReal_coe]
          exact ENat.toENNReal_le.mpr hle
  have hlim : ENNReal.ofReal (β - ε) ≤ F.tauAt P q :=
    le_limsup_of_le (h := fun b hb => by
      obtain ⟨n, hn1, hn2⟩ := (key.and hb).exists
      exact hn1.trans hn2)
  calc ENNReal.ofReal β = ENNReal.ofReal ((β - ε) + ε) := by rw [sub_add_cancel]
    _ ≤ ENNReal.ofReal (β - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (β - ε) + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ F.tauAt P q + ε := add_le_add hlim le_rfl

/-- For an increasing property it suffices to look at the single round `⌊(β - ε) n⌋`. -/
theorem le_tau_of_forall_eventually_of_increasing
    (hstep : ∀ n (S : F.Strat n), IsAppendStep (F.step n S))
    (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (hP : ∀ n, IncreasingProperty (P n)) {β : ℝ}
    {q : ℝ≥0∞} (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : F.Strat n,
      successProb (F.step n S) (P (n + 1)) ⌊(β - ε) * ((n + 1 : ℕ) : ℝ)⌋₊ < q) :
    ENNReal.ofReal β ≤ F.tau P := by
  refine F.le_tau_of_forall_eventually P hq fun ε hε => ?_
  filter_upwards [h ε hε] with n hn S t ht
  exact lt_of_le_of_lt
    (successProb_mono _ (hstep n S) (hP (n + 1)) (Nat.le_floor ht)) (hn S)

end ProcessFamily

/-! ## The two processes as families, and Lemma 3.1 -/

/-- The post-positional process: the original semi-random graph process. -/
def postPositional : ProcessFamily where
  Strat n := PostRandomStrategy (Fin (n + 1))
  step _ S := stepPost S

/-- The pre-positional process proposed by Wormald. -/
def prePositional : ProcessFamily where
  Strat n := PreRandomStrategy (Fin (n + 1))
  step _ S := stepPre S

theorem postPositional_step (n : ℕ) (S : PostRandomStrategy (Fin (n + 1))) :
    postPositional.step n S = stepPost S :=
  rfl

theorem prePositional_step (n : ℕ) (S : PreRandomStrategy (Fin (n + 1))) :
    prePositional.step n S = stepPre S :=
  rfl

theorem postPositional_isAppendStep (n : ℕ) (S : postPositional.Strat n) :
    IsAppendStep (postPositional.step n S) :=
  isAppendStep_stepPost S

theorem prePositional_isAppendStep (n : ℕ) (S : prePositional.Strat n) :
    IsAppendStep (prePositional.step n S) :=
  isAppendStep_stepPre S

/-- **Lemma 3.1**, hitting-time form: the copy of a pre-positional strategy reaches every
property with the same probabilities, so `τ_P(q, n)` is at most as large in the post-positional
process as in the pre-positional one. -/
theorem minHittingTime_post_le_pre (n : ℕ) (P : SimpleGraph (Fin (n + 1)) → Prop)
    (q : ℝ≥0∞) : postPositional.minHittingTime n P q ≤ prePositional.minHittingTime n P q := by
  refine le_iInf fun S => ?_
  refine (postPositional.minHittingTime_le n P q (liftPreRandom S)).trans (le_of_eq ?_)
  exact congrArg (fun T => hittingTime T P q) (stepPost_liftPreRandom S)

/-- **Lemma 3.1**: `τ_P^{post} ≤ τ_P^{pre}` for every property `P`. -/
theorem tau_post_le_pre (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) :
    postPositional.tau P ≤ prePositional.tau P := by
  unfold ProcessFamily.tau
  refine iSup₂_mono fun q _ => ?_
  unfold ProcessFamily.tauAt
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  exact ENNReal.div_le_div_right (ENat.toENNReal_mono (minHittingTime_post_le_pre n _ q)) _

/-! ## `k`-connectivity (Section 4) -/

/-- Section 4: a connected graph is `k`-connected if it remains connected when removing fewer
than `k` vertices.  (For `n → ∞` and fixed `k` this agrees with the usual convention, which
also requires more than `k` vertices.) -/
def IsKConnected (k : ℕ) (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ s : Finset V, s.card < k → (G.induce ((s : Set V)ᶜ)).Connected

/-- Adding edges preserves `k`-connectivity. -/
theorem IsKConnected.mono {k : ℕ} {G H : SimpleGraph V} (hGH : G ≤ H)
    (hG : IsKConnected k G) : IsKConnected k H :=
  ⟨hG.1.mono hGH, fun s hs => (hG.2 s hs).mono (SimpleGraph.comap_monotone _ hGH)⟩

theorem isKConnected_increasing (k : ℕ) :
    IncreasingProperty (IsKConnected k : SimpleGraph V → Prop) :=
  fun _ _ hGH hG => hG.mono hGH

/-- The property `C_k` of Section 4.2 on the vertex sets `[n]`. -/
def kConnectedProperty (k : ℕ) : ∀ n : ℕ, SimpleGraph (Fin n) → Prop :=
  fun _ G => IsKConnected k G

theorem kConnectedProperty_increasing (k n : ℕ) :
    IncreasingProperty (kConnectedProperty k n) :=
  isKConnected_increasing k

/-! ## The main theorem -/

/-- **Theorem 1.1** (Gao, Koerts).  For every fixed `k ≥ 1` there is a real number `α_k` such
that for every `ε > 0`: (a) no strategy in the post-positional or in the pre-positional process
constructs a `k`-connected graph in at most `(α_k - ε) n` rounds, a.a.s.; (b) there are
strategies in both processes constructing a `k`-connected graph in at most `(α_k + ε) n`
rounds, a.a.s.  Here `α_1 = 1` and, for `k ≥ 2`, `α_k` is the constant of Wormald's min-degree
process (Remark 1.2(c)). -/
theorem P106 (k : ℕ) (hk : 1 ≤ k) :
    ∃ α : ℝ, ∀ ε : ℝ, 0 < ε →
      (∀ S : ∀ n : ℕ, PostRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPost (S n)) (kConnectedProperty k (n + 1))
          ⌊(α - ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 0)) ∧
      (∀ S : ∀ n : ℕ, PreRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPre (S n)) (kConnectedProperty k (n + 1))
          ⌊(α - ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 0)) ∧
      (∃ S : ∀ n : ℕ, PostRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPost (S n)) (kConnectedProperty k (n + 1))
          ⌊(α + ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 1)) ∧
      (∃ S : ∀ n : ℕ, PreRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPre (S n)) (kConnectedProperty k (n + 1))
          ⌊(α + ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 1)) := by
  sorry

/-! ## Direct corollaries -/

/-- Theorem 1.1 restricted to the pre-positional process: it has a sharp linear threshold for
`k`-connectivity. -/
theorem kConnected_threshold_pre (k : ℕ) (hk : 1 ≤ k) :
    ∃ α : ℝ, ∀ ε : ℝ, 0 < ε →
      (∀ S : ∀ n : ℕ, PreRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPre (S n)) (kConnectedProperty k (n + 1))
          ⌊(α - ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 0)) ∧
      (∃ S : ∀ n : ℕ, PreRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPre (S n)) (kConnectedProperty k (n + 1))
          ⌊(α + ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 1)) := by
  obtain ⟨α, hα⟩ := P106 k hk
  exact ⟨α, fun ε hε => ⟨(hα ε hε).2.1, (hα ε hε).2.2.2⟩⟩

/-- Theorem 1.1 restricted to the post-positional process, the original semi-random graph
process: the case `k = 2` is the open case settled by the paper (Remark 1.2(a)). -/
theorem kConnected_threshold_post (k : ℕ) (hk : 1 ≤ k) :
    ∃ α : ℝ, ∀ ε : ℝ, 0 < ε →
      (∀ S : ∀ n : ℕ, PostRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPost (S n)) (kConnectedProperty k (n + 1))
          ⌊(α - ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 0)) ∧
      (∃ S : ∀ n : ℕ, PostRandomStrategy (Fin (n + 1)),
        Tendsto (fun n : ℕ => successProb (stepPost (S n)) (kConnectedProperty k (n + 1))
          ⌊(α + ε) * ((n + 1 : ℕ) : ℝ)⌋₊) atTop (𝓝 1)) := by
  obtain ⟨α, hα⟩ := P106 k hk
  exact ⟨α, fun ε hε => ⟨(hα ε hε).1, (hα ε hε).2.2.1⟩⟩

end PositionalSemiRandom
