import ProofBench.PROBLEMS.P107.P107
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- ---------------------------------------------------- -/
/- Paper: Sandwiching between random regular graphs and Erdős-Rényi graphs: -/
/-        configuration model and unions of perfect matchings -/
/- ---------------------------------------------------- -/

/-!
# P047: Sandwiching between random regular graphs and Erdős-Rényi graphs

This file formalizes the random graph models and the main theorem of

  P. Gao, M. Isaev and X. Pérez-Giménez, *Sandwiching between random regular
  graphs and Erdős-Rényi graphs: configuration model and unions of perfect
  matchings*, arXiv:2510.21472.

## The paper's dependency graph

* Section 1: the random regular graph `G(n, d)` (uniform on the `d`-regular
  simple graphs on `[n]`, `dn` even), the Erdős-Rényi graph `G(n, p)`, the
  configuration model `P(n, d)` and its loopless variant `P_*(n, d)`, and the
  unions `M^∪_d` and superpositions `M^+_d` of `d` independent uniform perfect
  matchings (Propositions 1.1-1.3).  Kim and Vu's sandwich conjecture and
  Proposition 1.4 (Gao, Isaev and McKay): for `min(d, n - d) ≫ log⁴ n` there
  are `p_*, p^* = (1 + o(1)) d/n` and a coupling `(G_*, G, G^*)` with
  `G_* ~ G(n, p_*)`, `G ~ G(n, d)`, `G^* ~ G(n, p^*)` and
  `P(G_* ⊆ G ⊆ G^*) = 1 - o(1)`.
* **Theorem 1.5**, the main theorem: (a) the sandwich of Proposition 1.4 for
  all `d = n - O(log⁴ n)`; (b) for `d ≫ log n` and `d = O(log⁴ n)`, a sandwich
  with `p_* = (1 - o(1)) d/n` and `p^* = (8 + o(1)) d/n`; (c) for
  `d = o(log n)` and every fixed `ε > 0`, an embedding `G ⊆ G^*` with
  `G^* ~ G(n, (1 + ε) log n / n)` for even `n` and `G(n, (2 + ε) log n / n)`
  for odd `n`; (d) for `d ≤ c log n`, the embedding of (c) with
  `p^* = C(c) log n / n`.
* Sections 1.1-1.3 and 3-7, the intermediate couplings: Theorem 1.6
  (`M^∪_d ⊆ G(n, p)` for `d ≤ (g(x) + o(1)) p n`, Section 7: Proposition 7.1,
  Lemma 7.2), Theorem 1.7 (`G(n, d) ⊆ M^∪_{τ(d)}`, `τ(d) = (2 + o(1)) d`),
  Theorem 1.8 (`P_*(n, d) ⊆ M^+_τ` and `G(n, d) ⊆ M^+_τ` for fixed `d ≥ 3`,
  Section 3: Lemmas 3.1-3.2, Claim 3.3), Theorems 1.9-1.10 (decomposition of
  `P_*(n, d + 1)` and `P_*(n, d + 2)`, Sections 4 and 6: Lemmas 4.1-4.5, 6.1,
  Claims 6.2-6.3, Corollary 6.4, Theorem 6.5, Corollary 6.6), Theorem 1.11
  (`P_*(n, d) ⊆ M^+_{τ(d)}`) and Corollary 1.7, Theorem 1.12
  (`G(n, d) ⊆ G[P^*]` for `P^* ~ P_*(n, d + 1)`, Section 5: Lemmas 5.1-5.2).
  Section 2 collects the tools: McKay's enumeration (Theorems 2.1-2.3),
  Strassen's theorem with deficiency (Theorem 2.4, Corollaries 2.5-2.6).
* Section 8, the proof of Theorem 1.5: for even `n`, parts (b)-(d) follow by
  chaining the lower embedding of [13] with Theorems 1.7 and 1.6 (or
  Theorem 1.8(b) and Theorem 1.6 for bounded `d`), and part (a) follows from
  (b)-(d) by taking complements; for odd `n`, Lemma 8.1 reduces to even `n - 1`.

## What is formalized here

The target of the problem is **Theorem 1.5**, stated at the end of this file as
`P104` and proved by `sorry`, the single `sorry` of the file.
Everything else is proved from first principles with no `sorry` and no new
axiom:

* `Sandwiched`, `GraphTriple`, `SandwichEvent`, `sandwichProbability`,
  `WithHighProbability` and the transfer lemmas: the order-theoretic interface
  of the first version of this file, kept unchanged;
* `regularSequence`, `randomRegularGraph`, `binomialGraph`: `G(n, d)` and
  `G(n, p)`, through the laws `G(n, d)` and `G(n, W)` of `P050`;
* `Coupling3`, `Coupling3.sandwichProb`: couplings of three laws and the
  probability of the sandwich event `G_* ⊆ G ⊆ G^*`, together with the
  projections to the two one-sided couplings;
* `logThreshold`: the edge probability of part (c), `(1 + ε) log n / n` for
  even `n` and `(2 + ε) log n / n` for odd `n`.

## What is deliberately not asserted

* The intermediate models `P(n, d)`, `P_*(n, d)`, `M^∪_d`, `M^+_d` and the
  couplings of Theorems 1.6-1.12 are not encoded; the file carries a single
  `sorry`.
* The constants `g` of Theorem 1.6 and `C(c)` of part (d) are only asserted
  to exist, as in the paper.

## Conventions

* The degree `d = d(n)` is a function of `n`; `G(n, d)` is defined for every
  `n` (with the junk value `⊥` of `P050` when `d` is not realisable), and the
  main theorem assumes that the constant sequence `(d, …, d)` is realisable,
  i.e. `d ≤ n - 1` and `dn` even, as the paper assumes throughout.
* Asymptotic conditions are `Filter.Tendsto` statements: `p = (c + o(1)) d/n`
  is `p / (d/n) → c`, `d ≫ log n` is `d / log n → ∞`, `d = o(log n)` is
  `d / log n → 0`, and `d = O(log⁴ n)` is "eventually `d ≤ C log⁴ n`".
* Probabilities live in `ℝ≥0∞`, and `P(G_* ⊆ G ⊆ G^*) = 1 - o(1)` is
  `sandwichProb → 1`.
-/

open Filter MeasureTheory

noncomputable section

namespace RandomGraphSandwich

variable {V : Type*}

/-- Samplewise graph sandwiching. -/
def Sandwiched (lower middle upper : SimpleGraph V) : Prop :=
  lower <= middle /\ middle <= upper

theorem sandwiched_refl (G : SimpleGraph V) : Sandwiched G G G :=
  ⟨le_rfl, le_rfl⟩

/-- A sandwich remains valid after weakening its lower graph or enlarging its
upper graph. -/
theorem Sandwiched.mono_outer
    {lower middle upper lower' upper' : SimpleGraph V}
    (h : Sandwiched lower middle upper)
    (hlower : lower' <= lower) (hupper : upper <= upper') :
    Sandwiched lower' middle upper' :=
  ⟨hlower.trans h.1, h.2.trans hupper⟩

/-- Taking graph complements reverses both containments.  This is the
deterministic reduction used for the co-dense regime. -/
theorem Sandwiched.compl
    {lower middle upper : SimpleGraph V}
    (h : Sandwiched lower middle upper) :
    Sandwiched upperᶜ middleᶜ lowerᶜ :=
  ⟨compl_le_compl h.2, compl_le_compl h.1⟩

/-- An increasing graph property is preserved when edges are added. -/
def IncreasingProperty (property : SimpleGraph V -> Prop) : Prop :=
  forall G H, G <= H -> property G -> property H

/-- A lower sandwich transfers every increasing property to the middle
graph. -/
theorem Sandwiched.property_of_lower
    {property : SimpleGraph V -> Prop}
    (hproperty : IncreasingProperty property)
    {lower middle upper : SimpleGraph V}
    (h : Sandwiched lower middle upper) (hlower : property lower) :
    property middle :=
  hproperty lower middle h.1 hlower

/-- Failure of an increasing property for the upper graph transfers to the
middle graph. -/
theorem Sandwiched.not_property_of_upper
    {property : SimpleGraph V -> Prop}
    (hproperty : IncreasingProperty property)
    {lower middle upper : SimpleGraph V}
    (h : Sandwiched lower middle upper) (hupper : Not (property upper)) :
    Not (property middle) := by
  intro hmiddle
  exact hupper (hproperty middle upper h.2 hmiddle)

/-- A coupled sample of the lower, target, and upper random graph models. -/
structure GraphTriple (V : Type*) where
  lower : SimpleGraph V
  middle : SimpleGraph V
  upper : SimpleGraph V

instance graphTripleMeasurableSpace (V : Type*) :
    MeasurableSpace (GraphTriple V) := ⊤

/-- The successful-containment event of a coupling. -/
def SandwichEvent (sample : GraphTriple V) : Prop :=
  Sandwiched sample.lower sample.middle sample.upper

/-- Real-valued probability that a coupling realizes its sandwich. -/
def sandwichProbability (law : Measure (GraphTriple V)) : Real :=
  law.real {sample | SandwichEvent sample}

/-- A sequence of coupling events holds asymptotically almost surely. -/
def WithHighProbability (probability : Nat -> Real) : Prop :=
  Tendsto probability atTop (nhds 1)

/-- Samplewise transfer through a successful coupling. -/
theorem property_transfer_on_event
    {property : SimpleGraph V -> Prop}
    (hproperty : IncreasingProperty property)
    (sample : GraphTriple V) (hsample : SandwichEvent sample) :
    property sample.lower -> property sample.middle :=
  (show Sandwiched sample.lower sample.middle sample.upper from hsample).property_of_lower
    hproperty

/-! ## The random graph models `G(n, d)` and `G(n, p)` -/

open SpecifiedDegreeEmbedding Topology
open scoped ENNReal

/-- The constant degree sequence `(d, …, d)` on `[n]`. -/
def regularSequence (n d : ℕ) : DegreeSequence n :=
  ⟨fun _ => d⟩

/-- The random regular graph `G(n, d)`: uniform on the `d`-regular simple graphs on `[n]`
(through the law `G(n, d)` of `P050`; the junk value `⊥` when `(d, …, d)` is not realisable). -/
def randomRegularGraph (n d : ℕ) : PMF (SimpleGraph (Fin n)) :=
  uniformDegreeGraph n (regularSequence n d)

/-- The Erdős-Rényi graph `G(n, p)`: every pair is an edge independently with probability
`p` (through the law `G(n, W)` of `P050` with the constant matrix). -/
def binomialGraph (n : ℕ) (p : ℝ) : PMF (SimpleGraph (Fin n)) :=
  independentEdgeGraph n (Matrix.of fun _ _ => p)

/-! ## Couplings of three laws -/

/-- A coupling of the laws `μ₁`, `μ₂`, `μ₃`: a joint law on triples with the prescribed
marginals. -/
structure Coupling3 {α : Type*} (μ₁ μ₂ μ₃ : PMF α) where
  /-- The joint law. -/
  joint : PMF (α × α × α)
  /-- The first marginal. -/
  map_fst : joint.map (fun x => x.1) = μ₁
  /-- The second marginal. -/
  map_snd : joint.map (fun x => x.2.1) = μ₂
  /-- The third marginal. -/
  map_thd : joint.map (fun x => x.2.2) = μ₃

/-- The probability of the sandwich event `G_* ⊆ G ⊆ G^*` under a coupling of three laws. -/
def Coupling3.sandwichProb {α : Type*} [LE α] {μ₁ μ₂ μ₃ : PMF α} (κ : Coupling3 μ₁ μ₂ μ₃) :
    ℝ≥0∞ :=
  κ.joint.toOuterMeasure {x | x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2}

theorem Coupling3.sandwichProb_le_one {α : Type*} [LE α] {μ₁ μ₂ μ₃ : PMF α}
    (κ : Coupling3 μ₁ μ₂ μ₃) : κ.sandwichProb ≤ 1 :=
  toOuterMeasure_le_one _ _

/-- The lower one-sided coupling `(G_*, G)` of a coupling of three laws. -/
noncomputable def Coupling3.lower {α : Type*} {μ₁ μ₂ μ₃ : PMF α} (κ : Coupling3 μ₁ μ₂ μ₃) :
    Coupling μ₁ μ₂ where
  joint := κ.joint.map fun x => (x.1, x.2.1)
  map_fst := by
    rw [PMF.map_comp]
    exact κ.map_fst
  map_snd := by
    rw [PMF.map_comp]
    exact κ.map_snd

/-- The upper one-sided coupling `(G, G^*)` of a coupling of three laws. -/
noncomputable def Coupling3.upper {α : Type*} {μ₁ μ₂ μ₃ : PMF α} (κ : Coupling3 μ₁ μ₂ μ₃) :
    Coupling μ₂ μ₃ where
  joint := κ.joint.map fun x => (x.2.1, x.2.2)
  map_fst := by
    rw [PMF.map_comp]
    exact κ.map_snd
  map_snd := by
    rw [PMF.map_comp]
    exact κ.map_thd

/-- The sandwich event implies each one-sided embedding event. -/
theorem Coupling3.sandwichProb_le_embedProb_lower {α : Type*} [LE α] {μ₁ μ₂ μ₃ : PMF α}
    (κ : Coupling3 μ₁ μ₂ μ₃) : κ.sandwichProb ≤ κ.lower.embedProb := by
  unfold Coupling3.sandwichProb Coupling.embedProb Coupling3.lower
  rw [PMF.toOuterMeasure_map_apply]
  exact κ.joint.toOuterMeasure_mono fun x hx => hx.1.1

theorem Coupling3.sandwichProb_le_embedProb_upper {α : Type*} [LE α] {μ₁ μ₂ μ₃ : PMF α}
    (κ : Coupling3 μ₁ μ₂ μ₃) : κ.sandwichProb ≤ κ.upper.embedProb := by
  unfold Coupling3.sandwichProb Coupling.embedProb Coupling3.upper
  rw [PMF.toOuterMeasure_map_apply]
  exact κ.joint.toOuterMeasure_mono fun x hx => hx.1.2

/-- The edge probability of Theorem 1.5(c): `(1 + ε) log n / n` for even `n` and
`(2 + ε) log n / n` for odd `n`. -/
def logThreshold (ε : ℝ) (n : ℕ) : ℝ :=
  (if Even n then 1 + ε else 2 + ε) * Real.log n / n

/-! ## The main theorem -/

/-- **Theorem 1.5** (Gao, Isaev, Pérez-Giménez).  Let `d = d(n)` be such that the constant
sequence `(d, …, d)` is realisable (`dn` even, `d ≤ n - 1`).
(a) If `d = n - O(log⁴ n)`, there are `p_*, p^* = (1 + o(1)) d/n` and couplings
`(G_*, G, G^*)` with `G_* ~ G(n, p_*)`, `G ~ G(n, d)`, `G^* ~ G(n, p^*)` and
`P(G_* ⊆ G ⊆ G^*) = 1 - o(1)` (Proposition 1.4, the Kim-Vu sandwich conjecture, in the
regime of very large degrees).
(b) If `d ≫ log n` and `d = O(log⁴ n)`, the same holds with `p_* = (1 - o(1)) d/n` and
`p^* = (8 + o(1)) d/n`.
(c) If `d = o(log n)`, then for every fixed `ε > 0` there are couplings `(G, G^*)` with
`G ~ G(n, d)`, `G^* ~ G(n, (1 + ε) log n / n)` for even `n` and `G(n, (2 + ε) log n / n)` for
odd `n`, and `P(G ⊆ G^*) = 1 - o(1)`.
(d) If `d ≤ c log n` for a fixed `c > 0`, there is `C(c) > 0` depending only on `c` such that
the coupling of (c) exists with `p^* = C(c) log n / n`. -/
theorem P104 :
    (∀ d : ℕ → ℕ, (∀ n, (regularSequence n (d n)).IsGraphical) →
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) - d n ≤ C * (Real.log n) ^ 4) →
      ∃ pLow pUp : ℕ → ℝ,
        Tendsto (fun n : ℕ => pLow n / ((d n : ℝ) / n)) atTop (𝓝 1) ∧
        Tendsto (fun n : ℕ => pUp n / ((d n : ℝ) / n)) atTop (𝓝 1) ∧
        ∃ κ : ∀ n : ℕ, Coupling3 (binomialGraph n (pLow n)) (randomRegularGraph n (d n))
            (binomialGraph n (pUp n)),
          Tendsto (fun n => (κ n).sandwichProb) atTop (𝓝 1)) ∧
    (∀ d : ℕ → ℕ, (∀ n, (regularSequence n (d n)).IsGraphical) →
      Tendsto (fun n : ℕ => (d n : ℝ) / Real.log n) atTop atTop →
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ C * (Real.log n) ^ 4) →
      ∃ pLow pUp : ℕ → ℝ,
        Tendsto (fun n : ℕ => pLow n / ((d n : ℝ) / n)) atTop (𝓝 1) ∧
        Tendsto (fun n : ℕ => pUp n / ((d n : ℝ) / n)) atTop (𝓝 8) ∧
        ∃ κ : ∀ n : ℕ, Coupling3 (binomialGraph n (pLow n)) (randomRegularGraph n (d n))
            (binomialGraph n (pUp n)),
          Tendsto (fun n => (κ n).sandwichProb) atTop (𝓝 1)) ∧
    (∀ d : ℕ → ℕ, (∀ n, (regularSequence n (d n)).IsGraphical) →
      Tendsto (fun n : ℕ => (d n : ℝ) / Real.log n) atTop (𝓝 0) →
      ∀ ε : ℝ, 0 < ε →
        ∃ κ : ∀ n : ℕ, Coupling (randomRegularGraph n (d n)) (binomialGraph n (logThreshold ε n)),
          Tendsto (fun n => (κ n).embedProb) atTop (𝓝 1)) ∧
    (∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ → ℕ, (∀ n, (regularSequence n (d n)).IsGraphical) →
        (∀ᶠ n : ℕ in atTop, (d n : ℝ) ≤ c * Real.log n) →
        ∃ κ : ∀ n : ℕ, Coupling (randomRegularGraph n (d n))
            (binomialGraph n (C * Real.log n / n)),
          Tendsto (fun n => (κ n).embedProb) atTop (𝓝 1)) := by
  sorry

/-! ## Direct corollaries -/

/-- **Theorem 1.5(a)**: the Kim-Vu sandwich conjecture for `d = n - O(log⁴ n)`. -/
theorem sandwich_theorem_dense (d : ℕ → ℕ) (hgraph : ∀ n, (regularSequence n (d n)).IsGraphical)
    (hd : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) - d n ≤ C * (Real.log n) ^ 4) :
    ∃ pLow pUp : ℕ → ℝ,
      Tendsto (fun n : ℕ => pLow n / ((d n : ℝ) / n)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => pUp n / ((d n : ℝ) / n)) atTop (𝓝 1) ∧
      ∃ κ : ∀ n : ℕ, Coupling3 (binomialGraph n (pLow n)) (randomRegularGraph n (d n))
          (binomialGraph n (pUp n)),
        Tendsto (fun n => (κ n).sandwichProb) atTop (𝓝 1) :=
  P104.1 d hgraph hd

/-- **Theorem 1.5(c)** for every confidence level: for `d = o(log n)` and `ε > 0`, the
couplings embed `G(n, d)` into `G(n, (1 + ε) log n / n)` (even `n`) or
`G(n, (2 + ε) log n / n)` (odd `n`) with probability more than `q` for all large `n`. -/
theorem sandwich_theorem_sparse (d : ℕ → ℕ)
    (hgraph : ∀ n, (regularSequence n (d n)).IsGraphical)
    (hd : Tendsto (fun n : ℕ => (d n : ℝ) / Real.log n) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ∀ n : ℕ, Coupling (randomRegularGraph n (d n)) (binomialGraph n (logThreshold ε n)),
      ∀ q : ℝ≥0∞, q < 1 → ∀ᶠ n : ℕ in atTop, q < (κ n).embedProb := by
  obtain ⟨κ, hκ⟩ := P104.2.2.1 d hgraph hd ε hε
  exact ⟨κ, fun q hq => (tendsto_order.1 hκ).1 q hq⟩

end RandomGraphSandwich
