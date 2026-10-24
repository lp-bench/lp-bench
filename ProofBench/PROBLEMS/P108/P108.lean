import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.SemiRandomProcess
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

namespace BuildingHamiltonianCycles

open PerfectMatchingSemiRandom Filter Topology
open scoped ENNReal NNReal

variable {V : Type*}

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

/-- `HAM` is an increasing property. -/
theorem hasHamiltonianCycle_increasing :
    IncreasingProperty (HasHamiltonianCycle : SimpleGraph V → Prop) := by
  intro G H hGH
  exact hasHamiltonianCycle_mono hGH

/-- Every Hamiltonian graph is connected. -/
theorem connected_of_hasHamiltonianCycle (G : SimpleGraph V)
    (hG : HasHamiltonianCycle G) : G.Connected :=
  hG.connected

end Hamiltonian

/-- The history of a play: the pairs `(u_i, v_i)` of offered vertex and response, in
chronological order. -/
abbrev History (V : Type*) := List (V × V)

/-- A strategy: for the history `(u_1, v_1, …, u_{t-1}, v_{t-1})` and the offered vertex `u_t`,
the distribution `s_t` on `[n] \ {u_t}` from which the response `v_t` is drawn.  The rule
`v_t ≠ u_t` is built into the type; the strategy sees the whole history but no future offers. -/
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

/-- The lifted strategy ignores the history. -/
@[simp]
theorem liftHistoryIndependent_apply (strategy : HistoryIndependentStrategy V)
    (history : History V) (offered : V) :
    liftHistoryIndependent strategy history offered = strategy offered :=
  rfl

/-- The lifted strategy answers with a point mass. -/
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

/-- The empty history gives the empty graph. -/
@[simp]
theorem historyGraph_nil : historyGraph ([] : History V) = ⊥ :=
  rfl

/-- The pair `(u, v)` contributes the edge `uv`. -/
@[simp]
theorem historyGraph_cons (u v : V) (history : History V) :
    historyGraph ((u, v) :: history) = addEdge (historyGraph history) u v :=
  rfl

/-- The graph of a concatenation is the union of the two graphs. -/
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

/-- Extending a history only adds edges. -/
theorem historyGraph_mono_of_prefix {h₁ h₂ : History V} (hp : h₁ <+: h₂) :
    historyGraph h₁ ≤ historyGraph h₂ := by
  obtain ⟨t, rfl⟩ := hp
  exact historyGraph_le_append h₁ t

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

/-- The two runs of `runDeterministicFrom_lift_eq` build the same graph. -/
theorem historyGraph_runDeterministicFrom_lift (strategy : HistoryIndependentStrategy V)
    (history : History V) (offers : List V) :
    historyGraph (runDeterministicFrom (liftHistoryIndependent strategy) history offers) =
      historyGraph (runHistoryIndependentFrom strategy history offers) := by
  rw [runDeterministicFrom_lift_eq]

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

/-- After `0` rounds the history is `h₀`. -/
@[simp]
theorem playLawFrom_zero (S : Strategy V) (h₀ : History V) :
    playLawFrom S h₀ 0 = PMF.pure h₀ :=
  rfl

/-- Round `t + 1` is one `step` after round `t`. -/
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

/-- After `t` rounds the history has grown by exactly `t` pairs. -/
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

/-- The starting history is a prefix of every history reached. -/
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

/-- `P[G_t ∈ P]` for the process started from the history `h₀`. -/
def successProbFrom (S : Strategy V) (h₀ : History V) (P : SimpleGraph V → Prop) (t : ℕ) :
    ℝ≥0∞ :=
  (playLawFrom S h₀ t).toOuterMeasure {h | P (historyGraph h)}

/-- `P[G_t ∈ P]` for the process started from the empty graph. -/
def successProb (S : Strategy V) (P : SimpleGraph V → Prop) (t : ℕ) : ℝ≥0∞ :=
  successProbFrom S [] P t

/-- Success probabilities are at most `1`. -/
theorem successProbFrom_le_one (S : Strategy V) (h₀ : History V) (P : SimpleGraph V → Prop)
    (t : ℕ) : successProbFrom S h₀ P t ≤ 1 := by
  unfold successProbFrom
  calc (playLawFrom S h₀ t).toOuterMeasure {h | P (historyGraph h)}
      ≤ (playLawFrom S h₀ t).toOuterMeasure Set.univ :=
        (playLawFrom S h₀ t).toOuterMeasure_mono fun x _ => Set.mem_univ x
    _ = 1 := (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _)

/-- Success probabilities are at most `1`. -/
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

/-- For an increasing property, `P[G_t ∈ P]` is non-decreasing in `t`. -/
theorem successProbFrom_mono (S : Strategy V) (h₀ : History V) {P : SimpleGraph V → Prop}
    (hP : IncreasingProperty P) : Monotone (successProbFrom S h₀ P) :=
  monotone_nat_of_le_succ (successProbFrom_le_succ S h₀ hP)

/-- For an increasing property, `P[G_t ∈ P]` is non-decreasing in `t`. -/
theorem successProb_mono (S : Strategy V) {P : SimpleGraph V → Prop}
    (hP : IncreasingProperty P) : Monotone (successProb S P) :=
  successProbFrom_mono S [] hP

/-- `m_P(S, q, n)`: the least round `t` with `P[G_t ∈ P] ≥ q`, and `∞` if there is none. -/
def hittingTime (S : Strategy V) (P : SimpleGraph V → Prop) (q : ℝ≥0∞) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : q ≤ successProb S P t), (t : ℕ∞)

/-- `m_P(S, q, n) ≤ t` as soon as round `t` reaches probability `q`. -/
theorem hittingTime_le {S : Strategy V} {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {t : ℕ}
    (h : q ≤ successProb S P t) : hittingTime S P q ≤ t := by
  unfold hittingTime
  exact iInf₂_le t h

/-- If every round reaching probability `q` is at least `m`, then `m ≤ m_P(S, q, n)`. -/
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

/-- `m_P(q, n) ≤ m_P(S, q, n)` for every strategy `S`. -/
theorem minHittingTime_le (P : SimpleGraph V → Prop) (q : ℝ≥0∞) (S : Strategy V) :
    minHittingTime V P q ≤ hittingTime S P q :=
  iInf_le _ S

/-- A lower bound on every `m_P(S, q, n)` bounds `m_P(q, n)`. -/
theorem le_minHittingTime {P : SimpleGraph V → Prop} {q : ℝ≥0∞} {m : ℕ∞}
    (h : ∀ S : Strategy V, m ≤ hittingTime S P q) : m ≤ minHittingTime V P q :=
  le_iInf h

/-- `m_P(q, n)` is non-decreasing in `q`, as observed in Section 1.1. -/
theorem minHittingTime_mono (P : SimpleGraph V → Prop) : Monotone (minHittingTime V P) :=
  fun _ _ hq => iInf_mono fun S => hittingTime_mono S P hq

end Process

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

/-- `limsup_n m_P(q, n) / n` is non-decreasing in `q`. -/
theorem roundConstantAt_mono (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) :
    Monotone (roundConstantAt P) := by
  intro q₁ q₂ hq
  unfold roundConstantAt
  refine limsup_le_limsup (Eventually.of_forall fun n => ?_)
  exact ENNReal.div_le_div_right (ENat.toENNReal_mono (minHittingTime_mono _ hq)) _

/-- For `0 < q < 1`, `limsup_n m_P(q, n) / n` is at most `C_P`. -/
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

/-- If for every `ε > 0` there are strategies `S_n` such that `P` holds after `⌈(α + ε) n⌉`
rounds with probability tending to `1`, then `C_P ≤ α`. -/
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

/-- If for some `0 < q < 1` and every `ε > 0`, eventually no strategy achieves `P` with
probability `q` within `(β - ε) n` rounds, then `C_P ≥ β`. -/
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

/-- The property `HAM` on the vertex set `[n]`, through `HasHamiltonianCycle`. -/
def hamiltonianProperty : ∀ n : ℕ, SimpleGraph (Fin n) → Prop :=
  fun _ G => HasHamiltonianCycle G

/-- `HAM` on `[n]` is an increasing property. -/
theorem hamiltonianProperty_increasing (n : ℕ) : IncreasingProperty (hamiltonianProperty n) :=
  hasHamiltonianCycle_increasing

/-- Decimal literals of `ℝ≥0∞` are the images of the corresponding real literals. -/
theorem ofReal_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ENNReal.ofReal (OfScientific.ofScientific m s e : ℝ) =
      (OfScientific.ofScientific m s e : ℝ≥0∞) := by
  rw [← NNReal.coe_ofScientific, ENNReal.ofReal_coe_nnreal]
  rfl

/-- Theorem 1.1 of Frieze–Gao–MacRury–Prałat–Sorkin, arXiv:2311.05533: `C_HAM ≤ 1.81701`, i.e.
for every `q < 1` and `ε > 0`, for all large `n` some strategy builds a Hamiltonian cycle on
`[n]` with probability at least `q` within `(1.81701 + ε) n` rounds. -/
theorem P108 : roundConstant hamiltonianProperty ≤ 1.81701 := by
  sorry

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

/-- Theorem 1.1 improves the bound `C_HAM ≤ 1.84887` of Frieze and Sorkin (Theorem 2.6 of the
paper). -/
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

section PlayInterface

open MeasureTheory

variable [Fintype V] [DecidableEq V]

/-- Not used by the main theorem: a deterministic adaptive strategy on realised plays. -/
abbrev AdaptiveStrategy (V : Type*) := List (V × V) → V → V

/-- Not used by the main theorem: the probability that a length-`T` play is Hamiltonian. -/
def hamiltonicityProbability {T : ℕ} (law : Measure (Play V T)) : ℝ :=
  successProbability law HasHamiltonianCycle

/-- Not used by the main theorem: a family of fixed-round laws is Hamiltonian a.a.s. -/
def BuildsHamiltonianWithHighProbability
    (rounds : ℕ → ℕ)
    (law : ∀ n, Measure (Play (Fin n) (rounds n))) : Prop :=
  Tendsto (fun n => hamiltonicityProbability (law n)) atTop (nhds 1)

/-- Not used by the main theorem: the a.a.s. property depends only on the probabilities. -/
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

/-- Not used by the main theorem: supergraphs of a Hamiltonian play graph are Hamiltonian. -/
theorem remains_hamiltonian_in_supergraph
    {T : ℕ} (play : Play V T) {H : SimpleGraph V}
    (hplay : HasHamiltonianCycle play.graph) (hle : play.graph ≤ H) :
    HasHamiltonianCycle H :=
  hasHamiltonianCycle_mono hle hplay

end PlayInterface

end BuildingHamiltonianCycles
