import ProofBench.PROBLEMS.P105.P105
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.ENNReal.Lemmas

/- ---------------------------------------------------- -/
/- Paper: Building Hamiltonian Cycles in the Semi-Random Graph Process in Less Than 2n Rounds -/
/- ---------------------------------------------------- -/

/-!
# P051: Building Hamiltonian cycles in the semi-random graph process in less than `2n` rounds

This file formalizes the semi-random graph process of Section 1.1 and the main
theorem of

  A. Frieze, P. Gao, C. MacRury, P. Prałat and G. B. Sorkin, *Building
  Hamiltonian cycles in the semi-random graph process in less than `2n`
  rounds*, arXiv:2311.05533.

## The paper's dependency graph

* Section 1.1: the semi-random graph process.  In round `t` a vertex `u_t` is
  offered uniformly at random, the online algorithm answers with a vertex
  `v_t ∈ [n] \ {u_t}` and the edge `u_t v_t` is added.  A strategy is a family of
  distributions `s_t(u_1, v_1, …, u_{t-1}, v_{t-1}, u_t)` on `[n] \ {u_t}` from
  which `v_t` is drawn.  For an increasing property `P` and `0 < q < 1`,
  `m_P(S, q, n)` is the least `t` with `P[G_t ∈ P] ≥ q` (`∞` if there is none),
  `m_P(q, n) = inf_S m_P(S, q, n)` and, equation (1),
  `C_P = lim_{q → 1⁻} limsup_{n → ∞} m_P(q, n) / n`.
* **Theorem 1.1**, the main theorem: `C_HAM ≤ α ≤ 1.81701`, where `α` is
  derived from the differential equations (6)-(9) and (17)-(21).
* Theorem 1.2, the second main result: `C_HAM ≥ β ≈ 1.26575`, proved in
  Section 3 (Claim 3.1, Lemma 3.2).
* Section 2, the proof of Theorem 1.1.  The strategy runs `DegreeGreedy`
  (Sections 2.5-2.6, analysed in Lemma 2.7, itself proved in Section 2.8 from
  Lemma 2.8, Lemma 2.9 and Proposition 2.10 by the differential equation method
  of Appendix A), then `FullyRandomized` (Section 2.3, Lemmas 2.1-2.3 and
  Proposition 2.4), which together leave a path on `(1 - o(1)) n` vertices after
  `(σ_N + α* + o(1)) n` rounds, and finally the clean-up algorithm of
  Section 2.4 (Lemma 2.5, Remark 2), which completes a Hamiltonian cycle in
  `o(n)` further rounds.  Theorem 2.6 is the `N = 0` case, `C_HAM ≤ 1.84887`.

## What is formalized here

The target of the problem is **Theorem 1.1**, stated at the end of this file as
`P108` and proved by `sorry`, the single `sorry` of the
file.  Everything else is proved from first principles with no `sorry` and no
new axiom:

* `History`, `Strategy`, `historyGraph`: histories `(u_1, v_1, …, u_t, v_t)`,
  strategies as history-dependent distributions on `[n] \ {u_t}` (the response
  type `{v // v ≠ u_t}` enforces the paper's rule that the algorithm may not
  answer with the offered vertex), and the underlying simple graph of a history
  (multiplicities discarded, which does not affect Hamiltonicity for `n ≥ 3`);
* `step`, `playLawFrom`, `playLaw`: the law of the process, built round by
  round from the uniform offer and the strategy's response; `playLawFrom_add`
  is the Markov property of the process;
* `successProbFrom`, `successProb`: `P[G_t ∈ P]`, monotone in `t` for an
  increasing property (`successProb_mono`);
* `hittingTime`, `minHittingTime`, `roundConstantAt`, `roundConstant`:
  `m_P(S, q, n)`, `m_P(q, n)`, `limsup_n m_P(q, n) / n` and `C_P`, valued in
  `ℕ∞` and `ℝ≥0∞` so that the paper's value `∞` is available.  `C_P` is defined
  as the supremum over `0 < q < 1`, and `tendsto_roundConstantAt` proves that
  this is the paper's left limit `lim_{q → 1⁻}` (the function is
  non-decreasing in `q`, as the paper observes);
* `roundConstant_le_of_forall_exists_tendsto`: the bridge from "for every
  `ε > 0` some strategies satisfy `P` a.a.s. after `(α + ε) n` rounds" to
  `C_P ≤ α`, the step by which the paper passes from Proposition 2.4 and
  Lemma 2.5 to Theorems 1.1 and 2.6; `le_roundConstant_of_forall_eventually` is
  the converse bridge used for lower bounds such as Theorem 1.2;
* `HasHamiltonianCycle`, `hamiltonianProperty`: the property `HAM`, through
  Mathlib's `SimpleGraph.IsHamiltonian`.

## What is deliberately not asserted

* The constant `α` of Theorem 1.1 is only characterised numerically in the
  paper (the solutions of the differential equations are computed in Julia); the
  theorem is stated with the printed bound `1.81701`.  The abstract and the
  proof in Section 2.7 give the slightly sharper `1.81696`, which implies the
  printed bound; the statement here follows the theorem as printed.
* Theorem 1.2 is a second main result; it is not stated here since the file
  carries a single `sorry`.  The bridge lemma it needs is proved.
* Nothing about running time or explicitness of the strategies is encoded.

## Conventions

* The process is defined over an arbitrary nonempty finite vertex type; `C_P`
  uses `Fin (n + 2)`, i.e. the vertex sets `[n]` with `n ≥ 2`.  The paper
  allows `n ≥ 1`, but on a single vertex no response `v_t ≠ u_t` exists, so
  there is no strategy at all and `m_P(q, 1) = ∞`; the `limsup` does not see
  this term, and starting at `n = 2` keeps the strategy sequences of the
  bridge lemmas well defined.
* Probabilities `q` live in `ℝ≥0∞` and `m_P(S, q, n)` in `ℕ∞`, as in the paper
  (`m_P(S, q, n) := ∞` if no round achieves probability `q`).
* The last section keeps the earlier interface of this file on the realized
  plays of `P048`; it is not used by the main theorem.
-/

noncomputable section

namespace BuildingHamiltonianCycles

open PerfectMatchingSemiRandom Filter Topology
open scoped ENNReal NNReal

variable {V : Type*}

/-! ## The property `HAM` -/

section Hamiltonian

variable [Fintype V] [DecidableEq V]

/-- The paper's increasing property `HAM`, using Mathlib's Hamiltonian-cycle
definition. -/
def HasHamiltonianCycle (G : SimpleGraph V) : Prop :=
  G.IsHamiltonian

/-- Hamiltonicity is preserved by adding edges. -/
theorem hasHamiltonianCycle_mono {G H : SimpleGraph V} (hGH : G ≤ H) :
    HasHamiltonianCycle G → HasHamiltonianCycle H := by
  intro hG
  exact hG.mono hGH

theorem hasHamiltonianCycle_increasing :
    IncreasingProperty (HasHamiltonianCycle : SimpleGraph V → Prop) := by
  intro G H hGH
  exact hasHamiltonianCycle_mono hGH

/-- Every Hamiltonian graph is connected. -/
theorem connected_of_hasHamiltonianCycle (G : SimpleGraph V)
    (hG : HasHamiltonianCycle G) : G.Connected :=
  hG.connected

end Hamiltonian

/-! ## Histories, strategies and the generated graph (Section 1.1) -/

/-- The history of a play: the pairs `(u_i, v_i)` of offered vertex and response, in
chronological order. -/
abbrev History (V : Type*) := List (V × V)

/-- A strategy of the paper: for the history `(u_1, v_1, …, u_{t-1}, v_{t-1})` and the offered
vertex `u_t` it prescribes the distribution `s_t(u_1, v_1, …, u_{t-1}, v_{t-1}, u_t)` on
`[n] \ {u_t}` from which the response `v_t` is drawn.  The paper's rule `v_t ≠ u_t` is built
into the type of the response.  Every strategy is online and fully adaptive: it may inspect
the whole history, but not the future offers. -/
abbrev Strategy (V : Type*) := History V → (offered : V) → PMF {v : V // v ≠ offered}

/-- A strategy answering deterministically (an atomic distribution `s_t`). -/
abbrev DeterministicStrategy (V : Type*) := History V → (offered : V) → {v : V // v ≠ offered}

/-- A strategy which sees the current offer but not the preceding history: the
*non-adaptive* strategies of Section 1.2, such as the simulation of the `3`-out process. -/
abbrev HistoryIndependentStrategy (V : Type*) := (offered : V) → {v : V // v ≠ offered}

/-- Every history-independent strategy is a deterministic strategy. -/
def liftHistoryIndependent (strategy : HistoryIndependentStrategy V) : DeterministicStrategy V :=
  fun _history offered => strategy offered

/-- Every deterministic strategy is a strategy. -/
def liftDeterministic (strategy : DeterministicStrategy V) : Strategy V :=
  fun history offered => PMF.pure (strategy history offered)

@[simp]
theorem liftHistoryIndependent_apply (strategy : HistoryIndependentStrategy V)
    (history : History V) (offered : V) :
    liftHistoryIndependent strategy history offered = strategy offered :=
  rfl

@[simp]
theorem liftDeterministic_apply (strategy : DeterministicStrategy V) (history : History V)
    (offered : V) :
    liftDeterministic strategy history offered = PMF.pure (strategy history offered) :=
  rfl

/-- The underlying simple graph of a history: repeated edges are discarded, as in the paper's
passage from the multigraph `G_t` to the graph in which a Hamiltonian cycle is sought. -/
def historyGraph : History V → SimpleGraph V
  | [] => ⊥
  | (offered, response) :: history => addEdge (historyGraph history) offered response

@[simp]
theorem historyGraph_nil : historyGraph ([] : History V) = ⊥ :=
  rfl

@[simp]
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

theorem historyGraph_mono_of_prefix {h₁ h₂ : History V} (hp : h₁ <+: h₂) :
    historyGraph h₁ ≤ historyGraph h₂ := by
  obtain ⟨t, rfl⟩ := hp
  exact historyGraph_le_append h₁ t

/-! ### Deterministic strategies against a fixed realization of the offers -/

/-- Run a deterministic strategy against a fixed sequence of offered vertices. -/
def runDeterministicFrom (strategy : DeterministicStrategy V) :
    History V → List V → History V
  | history, [] => history
  | history, offered :: offers =>
      runDeterministicFrom strategy
        (history ++ [(offered, (strategy history offered).1)]) offers

/-- Run a history-independent strategy against the same offers. -/
def runHistoryIndependentFrom (strategy : HistoryIndependentStrategy V) :
    History V → List V → History V
  | history, [] => history
  | history, offered :: offers =>
      runHistoryIndependentFrom strategy (history ++ [(offered, (strategy offered).1)]) offers

/-- The lifted strategy reproduces the history-independent strategy on every sample, not merely
in distribution. -/
theorem runDeterministicFrom_lift_eq (strategy : HistoryIndependentStrategy V)
    (history : History V) (offers : List V) :
    runDeterministicFrom (liftHistoryIndependent strategy) history offers =
      runHistoryIndependentFrom strategy history offers := by
  induction offers generalizing history with
  | nil => rfl
  | cons offered offers ih =>
      simp only [runDeterministicFrom, runHistoryIndependentFrom, liftHistoryIndependent]
      exact ih _

theorem historyGraph_runDeterministicFrom_lift (strategy : HistoryIndependentStrategy V)
    (history : History V) (offers : List V) :
    historyGraph (runDeterministicFrom (liftHistoryIndependent strategy) history offers) =
      historyGraph (runHistoryIndependentFrom strategy history offers) := by
  rw [runDeterministicFrom_lift_eq]

/-! ## The law of the semi-random process -/

section Process

variable [Fintype V] [Nonempty V]

/-- One round of the process from the history `history`: the offered vertex is uniform on the
vertex set, the response is drawn from the strategy (so it differs from the offered vertex),
and the pair is appended to the history. -/
def step (S : Strategy V) (history : History V) : PMF (History V) :=
  (PMF.uniformOfFintype V).bind fun offered =>
    (S history offered).bind fun response => PMF.pure (history ++ [(offered, response.1)])

/-- A round appends one pair whose response differs from the offered vertex. -/
theorem exists_of_mem_support_step {S : Strategy V} {history h : History V}
    (hh : h ∈ (step S history).support) :
    ∃ offered response : V, response ≠ offered ∧ h = history ++ [(offered, response)] := by
  simp only [step, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hh
  obtain ⟨offered, -, response, -, rfl⟩ := hh
  exact ⟨offered, response.1, response.2, rfl⟩

/-- The law of the history after `t` rounds of the process started from the history `h₀`. -/
def playLawFrom (S : Strategy V) (h₀ : History V) : ℕ → PMF (History V)
  | 0 => PMF.pure h₀
  | t + 1 => (playLawFrom S h₀ t).bind (step S)

/-- The law of the history after `t` rounds of the process started from the empty graph. -/
def playLaw (S : Strategy V) (t : ℕ) : PMF (History V) :=
  playLawFrom S [] t

@[simp]
theorem playLawFrom_zero (S : Strategy V) (h₀ : History V) :
    playLawFrom S h₀ 0 = PMF.pure h₀ :=
  rfl

@[simp]
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
      obtain ⟨u, v, -, rfl⟩ := exists_of_mem_support_step hstep
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
      obtain ⟨u, v, -, rfl⟩ := exists_of_mem_support_step hstep
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
      obtain ⟨u, v, -, rfl⟩ := exists_of_mem_support_step hh'
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

/-! ## The hitting times `m_P(S, q, n)` and `m_P(q, n)` -/

/-- `m_P(S, q, n)`: the least round `t` with `P[G_t ∈ P] ≥ q`, and `∞` if there is none. -/
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

/-- `m_P(S, q, n)` is non-decreasing in `q`. -/
theorem hittingTime_mono (S : Strategy V) (P : SimpleGraph V → Prop) :
    Monotone (hittingTime S P) := by
  intro q₁ q₂ hq
  unfold hittingTime
  exact iInf_mono fun _ => iInf_mono' fun h => ⟨hq.trans h, le_rfl⟩

variable (V) in
/-- `m_P(q, n) = inf_S m_P(S, q, n)`, the infimum over all strategies on the vertex set. -/
def minHittingTime (P : SimpleGraph V → Prop) (q : ℝ≥0∞) : ℕ∞ :=
  ⨅ S : Strategy V, hittingTime S P q

theorem minHittingTime_le (P : SimpleGraph V → Prop) (q : ℝ≥0∞) (S : Strategy V) :
    minHittingTime V P q ≤ hittingTime S P q :=
  iInf_le _ S

theorem le_minHittingTime {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {m : ℕ∞}
    (h : ∀ S : Strategy V, m ≤ hittingTime S P q) : m ≤ minHittingTime V P q :=
  le_iInf h

/-- `m_P(q, n)` is non-decreasing in `q`, as observed in Section 1.1. -/
theorem minHittingTime_mono (P : SimpleGraph V → Prop) : Monotone (minHittingTime V P) :=
  fun _ _ hq => iInf_mono fun S => hittingTime_mono S P hq

end Process

/-! ## The constant `C_P` of equation (1) -/

/-- `limsup_{n → ∞} m_P(q, n) / n`, over the vertex sets `[n] = Fin n`, `n ≥ 2`
(the index `n` of the `limsup` below is the paper's `n - 2`). -/
def roundConstantAt (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (q : ℝ≥0∞) : ℝ≥0∞ :=
  limsup (fun n : ℕ =>
    ((minHittingTime (Fin (n + 2)) (P (n + 2)) q : ℕ∞) : ℝ≥0∞) / ((n + 2 : ℕ) : ℝ≥0∞)) atTop

/-- `C_P = lim_{q → 1⁻} limsup_{n → ∞} m_P(q, n) / n`, equation (1) of the paper.  The function
of `q` is non-decreasing, so the left limit is the supremum over `0 < q < 1`;
`tendsto_roundConstantAt` below confirms that this is the paper's limit. -/
def roundConstant (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : ℝ≥0∞ :=
  ⨆ q ∈ Set.Ioo (0 : ℝ≥0∞) 1, roundConstantAt P q

theorem roundConstantAt_mono (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) :
    Monotone (roundConstantAt P) := by
  intro q₁ q₂ hq
  unfold roundConstantAt
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  exact ENNReal.div_le_div_right (ENat.toENNReal_mono (minHittingTime_mono _ hq)) _

theorem roundConstantAt_le_roundConstant (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) {q : ℝ≥0∞}
    (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1) : roundConstantAt P q ≤ roundConstant P := by
  unfold roundConstant
  exact le_iSup₂ (f := fun q _ => roundConstantAt P q) q hq

/-- `C_P` is the left limit at `q = 1` of `q ↦ limsup_n m_P(q, n) / n`, as in equation (1). -/
theorem tendsto_roundConstantAt (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) :
    Tendsto (roundConstantAt P) (𝓝[<] 1) (𝓝 (roundConstant P)) := by
  have h := (roundConstantAt_mono P).tendsto_nhdsLT 1
  convert h using 2
  apply le_antisymm
  · exact iSup₂_le fun q hq => le_sSup ⟨q, hq.2, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨q, hq, rfl⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ q) with hq0 | hq0
    · subst hq0
      calc roundConstantAt P 0 ≤ roundConstantAt P (1 / 2) := roundConstantAt_mono P zero_le
        _ ≤ roundConstant P :=
          roundConstantAt_le_roundConstant P ⟨ENNReal.half_pos one_ne_zero,
            ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top⟩
    · exact roundConstantAt_le_roundConstant P ⟨hq0, hq⟩

/-! ## From almost-sure statements to bounds on `C_P` -/

/-- **Upper bounds on `C_P` from a.a.s. statements.**  If for every `ε > 0` there are
strategies `S_n` such that `P` holds after `⌈(α + ε) n⌉` rounds with probability tending to
`1`, then `C_P ≤ α`.  This is how the paper passes from Proposition 2.4 and Lemma 2.5 to
Theorems 1.1 and 2.6. -/
theorem roundConstant_le_of_forall_exists_tendsto (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop)
    {α : ℝ} (hα : 0 ≤ α)
    (h : ∀ ε : ℝ, 0 < ε → ∃ S : ∀ n : ℕ, Strategy (Fin (n + 2)),
      Tendsto (fun n : ℕ => successProb (S n) (P (n + 2)) ⌈(α + ε) * ((n + 2 : ℕ) : ℝ)⌉₊)
        atTop (𝓝 1)) :
    roundConstant P ≤ ENNReal.ofReal α := by
  unfold roundConstant
  refine iSup₂_le fun q hq => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
  obtain ⟨S, hS⟩ := h ((ε : ℝ) / 2) hε2
  have hev : ∀ᶠ n : ℕ in atTop,
      q < successProb (S n) (P (n + 2)) ⌈(α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ)⌉₊ :=
    (tendsto_order.1 hS).1 q hq.2
  have hlin : Tendsto (fun n : ℕ => (ε : ℝ) / 2 * ((n + 2 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε2 (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have hev2 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (ε : ℝ) / 2 * ((n + 2 : ℕ) : ℝ) :=
    hlin.eventually_ge_atTop 1
  unfold roundConstantAt
  refine limsup_le_of_le (h := ?_)
  filter_upwards [hev, hev2] with n hn1 hn2
  have hm : ((minHittingTime (Fin (n + 2)) (P (n + 2)) q : ℕ∞) : ℝ≥0∞)
      ≤ ((⌈(α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) := by
    rw [← ENat.toENNReal_coe]
    exact ENat.toENNReal_le.mpr
      ((minHittingTime_le _ _ (S n)).trans (hittingTime_le hn1.le))
  have hreal : ((⌈(α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ)
      ≤ (α + (ε : ℝ)) * ((n + 2 : ℕ) : ℝ) := by
    have h1 := Nat.ceil_lt_add_one
      (mul_nonneg (add_nonneg hα hε2.le) (Nat.cast_nonneg (n + 2)) :
        (0 : ℝ) ≤ (α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ))
    have h2 : (α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ) + (ε : ℝ) / 2 * ((n + 2 : ℕ) : ℝ)
        = (α + (ε : ℝ)) * ((n + 2 : ℕ) : ℝ) := by ring
    linarith
  have hT : ((⌈(α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞)
      ≤ (ENNReal.ofReal α + ε) * ((n + 2 : ℕ) : ℝ≥0∞) := by
    calc ((⌈(α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal ((⌈(α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
          (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal ((α + (ε : ℝ)) * ((n + 2 : ℕ) : ℝ)) := ENNReal.ofReal_le_ofReal hreal
      _ = (ENNReal.ofReal α + ε) * ((n + 2 : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.ofReal_mul (add_nonneg hα ε.coe_nonneg), ENNReal.ofReal_add hα ε.coe_nonneg,
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]
  calc ((minHittingTime (Fin (n + 2)) (P (n + 2)) q : ℕ∞) : ℝ≥0∞) / ((n + 2 : ℕ) : ℝ≥0∞)
      ≤ ((⌈(α + (ε : ℝ) / 2) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) / ((n + 2 : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div_right hm _
    _ ≤ ENNReal.ofReal α + ε :=
        (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr (by omega))
          (ENNReal.natCast_ne_top _)).mpr hT

/-- **Lower bounds on `C_P` from a.a.s. statements.**  If for some `0 < q < 1` and every
`ε > 0`, eventually no strategy achieves `P` with probability `q` within `(β - ε) n` rounds,
then `C_P ≥ β`.  This is the shape of the proof of Theorem 1.2. -/
theorem le_roundConstant_of_forall_eventually (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop)
    {β : ℝ} {q : ℝ≥0∞} (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Strategy (Fin (n + 2)), ∀ t : ℕ,
      (t : ℝ) ≤ (β - ε) * ((n + 2 : ℕ) : ℝ) → successProb S (P (n + 2)) t < q) :
    ENNReal.ofReal β ≤ roundConstant P := by
  refine le_trans ?_ (roundConstantAt_le_roundConstant P hq)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have key : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (β - ε) ≤
      ((minHittingTime (Fin (n + 2)) (P (n + 2)) q : ℕ∞) : ℝ≥0∞) / ((n + 2 : ℕ) : ℝ≥0∞) := by
    filter_upwards [h ε (NNReal.coe_pos.mpr hε)] with n hn
    have hle : ((⌈(β - (ε : ℝ)) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℕ∞)
        ≤ minHittingTime (Fin (n + 2)) (P (n + 2)) q := by
      refine le_minHittingTime fun S => le_hittingTime fun t ht => ?_
      by_contra hcon
      have hlt : (t : ℝ) < (β - (ε : ℝ)) * ((n + 2 : ℕ) : ℝ) :=
        Nat.lt_ceil.mp (not_le.mp hcon)
      exact absurd ht (not_le.mpr (hn S t hlt.le))
    rw [ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr (by omega)))
      (Or.inl (ENNReal.natCast_ne_top _))]
    calc ENNReal.ofReal (β - ε) * ((n + 2 : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal ((β - (ε : ℝ)) * ((n + 2 : ℕ) : ℝ)) := by
          rw [ENNReal.ofReal_mul' (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ((⌈(β - (ε : ℝ)) * ((n + 2 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ ((minHittingTime (Fin (n + 2)) (P (n + 2)) q : ℕ∞) : ℝ≥0∞) := by
          rw [← ENat.toENNReal_coe]
          exact ENat.toENNReal_le.mpr hle
  have hlim : ENNReal.ofReal (β - ε) ≤ roundConstantAt P q :=
    le_limsup_of_le (h := fun b hb => by
      obtain ⟨n, hn1, hn2⟩ := (key.and hb).exists
      exact hn1.trans hn2)
  calc ENNReal.ofReal β = ENNReal.ofReal ((β - ε) + ε) := by rw [sub_add_cancel]
    _ ≤ ENNReal.ofReal (β - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (β - ε) + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ roundConstantAt P q + ε := add_le_add hlim le_rfl

/-- For an increasing property it suffices to look at the single round `⌊(β - ε) n⌋`. -/
theorem le_roundConstant_of_forall_eventually_of_increasing
    (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) (hP : ∀ n, IncreasingProperty (P n)) {β : ℝ}
    {q : ℝ≥0∞} (hq : q ∈ Set.Ioo (0 : ℝ≥0∞) 1)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ S : Strategy (Fin (n + 2)),
      successProb S (P (n + 2)) ⌊(β - ε) * ((n + 2 : ℕ) : ℝ)⌋₊ < q) :
    ENNReal.ofReal β ≤ roundConstant P := by
  refine le_roundConstant_of_forall_eventually P hq fun ε hε => ?_
  filter_upwards [h ε hε] with n hn S t ht
  exact lt_of_le_of_lt (successProb_mono S (hP (n + 2)) (Nat.le_floor ht)) (hn S)

/-! ## The property `HAM` on the vertex sets `[n]` -/

/-- The property `HAM` on the vertex set `[n]`, through `HasHamiltonianCycle`. -/
def hamiltonianProperty : ∀ n : ℕ, SimpleGraph (Fin n) → Prop :=
  fun _ G => HasHamiltonianCycle G

theorem hamiltonianProperty_increasing (n : ℕ) : IncreasingProperty (hamiltonianProperty n) :=
  hasHamiltonianCycle_increasing

/-- Decimal literals of `ℝ≥0∞` are the images of the corresponding real literals. -/
theorem ofReal_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ENNReal.ofReal (OfScientific.ofScientific m s e : ℝ) =
      (OfScientific.ofScientific m s e : ℝ≥0∞) := by
  rw [← NNReal.coe_ofScientific, ENNReal.ofReal_coe_nnreal]
  rfl

/-! ## The main theorem -/

/-- **Theorem 1.1** (Frieze, Gao, MacRury, Prałat, Sorkin).  `C_HAM ≤ 1.81701`: for every
`q < 1` and `ε > 0`, for all large `n` some strategy builds a Hamiltonian cycle on `[n]` with
probability at least `q` within `(1.81701 + ε) n` rounds of the semi-random graph process.  The
paper's constant `α ≤ 1.81701` is the numerical solution of the differential equations (6)-(9)
and (17)-(21), obtained by running `DegreeGreedy` (with `N = 100` phases), `FullyRandomized`,
and the clean-up algorithm of Section 2.4; the proof in Section 2.7 actually arrives at
`(σ_N + α* + o(1)) n ≤ 1.81696 n` rounds. -/
theorem P108 : roundConstant hamiltonianProperty ≤ 1.81701 := by
  sorry

/-! ## Direct corollaries -/

/-- `C_HAM` is finite. -/
theorem roundConstant_hamiltonian_ne_top : roundConstant hamiltonianProperty ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [← ofReal_ofScientific]; exact ENNReal.ofReal_ne_top)
    P108

/-- The claim of the title: a Hamiltonian cycle is built in less than `2n` rounds. -/
theorem roundConstant_hamiltonian_lt_two : roundConstant hamiltonianProperty < 2 :=
  lt_of_le_of_lt P108 (by
    rw [← ofReal_ofScientific, ← ENNReal.ofReal_ofNat 2,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num)

/-- Theorem 1.1 improves the bound `C_HAM ≤ 1.84887` of Theorem 2.6 (the `N = 0` case,
the bound of Frieze and Sorkin, reference [15] of the paper). -/
theorem roundConstant_hamiltonian_lt_fullyRandomized_bound :
    roundConstant hamiltonianProperty < 1.84887 :=
  lt_of_le_of_lt P108 (by
    rw [← ofReal_ofScientific, ← ofReal_ofScientific,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num)

/-- Theorem 1.1 improves the previously best fully adaptive bound `2.01678` of Gao, MacRury
and Prałat (reference [18] of the paper). -/
theorem roundConstant_hamiltonian_lt_previous_bound :
    roundConstant hamiltonianProperty < 2.01678 :=
  lt_of_le_of_lt P108 (by
    rw [← ofReal_ofScientific, ← ofReal_ofScientific,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    norm_num)

/-! ## The earlier interface on realized plays

The declarations below are the interface of the first version of this file, on the
fixed-length realized plays and measures of `P048`.  They are kept for reference and are
not used by the main theorem: the paper's quantities `m_P(S, q, n)` and `C_P` are defined
through the strategy-driven laws above. -/

section PlayInterface

open MeasureTheory

variable [Fintype V] [DecidableEq V]

/-- A deterministic fully adaptive strategy on realized plays: the response can inspect the
entire prior history and the currently offered vertex.  Unlike `DeterministicStrategy`, this
type does not enforce the paper's rule `v_t ≠ u_t`. -/
abbrev AdaptiveStrategy (V : Type*) := List (V × V) → V → V

/-- Probability that a length-`T` play has built a Hamiltonian graph. -/
def hamiltonicityProbability {T : ℕ} (law : Measure (Play V T)) : ℝ :=
  successProbability law HasHamiltonianCycle

/-- A family of fixed-round laws succeeds asymptotically almost surely. -/
def BuildsHamiltonianWithHighProbability
    (rounds : ℕ → ℕ)
    (law : ∀ n, Measure (Play (Fin n) (rounds n))) : Prop :=
  Tendsto (fun n => hamiltonicityProbability (law n)) atTop (nhds 1)

theorem buildsHamiltonianWithHighProbability_congr
    {rounds : ℕ → ℕ}
    {law law' : ∀ n, Measure (Play (Fin n) (rounds n))}
    (h : ∀ n,
      hamiltonicityProbability (law n) =
        hamiltonicityProbability (law' n)) :
    BuildsHamiltonianWithHighProbability rounds law ↔
      BuildsHamiltonianWithHighProbability rounds law' := by
  unfold BuildsHamiltonianWithHighProbability
  rw [show (fun n => hamiltonicityProbability (law n)) =
      (fun n => hamiltonicityProbability (law' n)) from funext h]

/-- Once a play's graph is Hamiltonian, every supergraph produced by later
rounds remains Hamiltonian. -/
theorem remains_hamiltonian_in_supergraph
    {T : ℕ} (play : Play V T) {H : SimpleGraph V}
    (hplay : HasHamiltonianCycle play.graph) (hle : play.graph ≤ H) :
    HasHamiltonianCycle H :=
  hasHamiltonianCycle_mono hle hplay

end PlayInterface

end BuildingHamiltonianCycles
