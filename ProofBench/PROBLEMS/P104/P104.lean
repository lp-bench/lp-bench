import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.RandomGraphs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter MeasureTheory

noncomputable section

namespace RandomGraphSandwich

variable {V : Type*}

/-- The containments `lower ⊆ middle ⊆ upper` of graphs. -/
def Sandwiched (lower middle upper : SimpleGraph V) : Prop :=
  lower <= middle /\ middle <= upper

/-- Every graph is sandwiched between two copies of itself. -/
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

/-- Taking graph complements reverses both containments. -/
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

open SpecifiedDegreeEmbedding Topology
open scoped ENNReal

/-- The constant degree sequence `(d, …, d)` on `[n]`. -/
def regularSequence (n d : ℕ) : DegreeSequence n :=
  ⟨fun _ => d⟩

/-- The random regular graph `G(n, d)`: uniform on the `d`-regular simple graphs on `[n]`
(with the junk value `⊥` when `(d, …, d)` is not realisable). -/
def randomRegularGraph (n d : ℕ) : PMF (SimpleGraph (Fin n)) :=
  uniformDegreeGraph n (regularSequence n d)

/-- The Erdős-Rényi graph `G(n, p)`: every pair is an edge independently with probability
`p` (a value of `p` outside `[0, 1]` is clamped to that interval). -/
def binomialGraph (n : ℕ) (p : ℝ) : PMF (SimpleGraph (Fin n)) :=
  independentEdgeGraph n (Matrix.of fun _ _ => p)

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

/-- The probability of the sandwich event `G_* ⊆ G ⊆ G^*` under a coupling of three laws;
`P(G_* ⊆ G ⊆ G^*) = 1 - o(1)` is stated as `sandwichProb → 1`. -/
def Coupling3.sandwichProb {α : Type*} [LE α] {μ₁ μ₂ μ₃ : PMF α} (κ : Coupling3 μ₁ μ₂ μ₃) :
    ℝ≥0∞ :=
  κ.joint.toOuterMeasure {x | x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2}

/-- The sandwich probability is at most one. -/
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

/-- The sandwich event implies the lower embedding event `G_* ⊆ G`. -/
theorem Coupling3.sandwichProb_le_embedProb_lower {α : Type*} [LE α] {μ₁ μ₂ μ₃ : PMF α}
    (κ : Coupling3 μ₁ μ₂ μ₃) : κ.sandwichProb ≤ κ.lower.embedProb := by
  unfold Coupling3.sandwichProb Coupling.embedProb Coupling3.lower
  rw [PMF.toOuterMeasure_map_apply]
  exact κ.joint.toOuterMeasure_mono fun x hx => hx.1.1

/-- The sandwich event implies the upper embedding event `G ⊆ G^*`. -/
theorem Coupling3.sandwichProb_le_embedProb_upper {α : Type*} [LE α] {μ₁ μ₂ μ₃ : PMF α}
    (κ : Coupling3 μ₁ μ₂ μ₃) : κ.sandwichProb ≤ κ.upper.embedProb := by
  unfold Coupling3.sandwichProb Coupling.embedProb Coupling3.upper
  rw [PMF.toOuterMeasure_map_apply]
  exact κ.joint.toOuterMeasure_mono fun x hx => hx.1.2

/-- The edge probability of Theorem 1.5(c): `(1 + ε) log n / n` for even `n` and
`(2 + ε) log n / n` for odd `n`. -/
def logThreshold (ε : ℝ) (n : ℕ) : ℝ :=
  (if Even n then 1 + ε else 2 + ε) * Real.log n / n

/-- **Theorem 1.5** of Gao–Isaev–Pérez-Giménez, arXiv:2510.21472, for realisable `d = d(n)`:
(a) if `d = n - O(log⁴ n)`, a.a.s. `G(n, p_*) ⊆ G(n, d) ⊆ G(n, p^*)` with `p_*, p^* ~ d/n`;
(b) if `log n ≪ d = O(log⁴ n)`, the same with `p_* ~ d/n`, `p^* ~ 8d/n`; (c) if `d = o(log n)`,
a.a.s. `G(n, d) ⊆ G(n, logThreshold ε n)`; (d) if `d ≤ c log n`, the same with `C(c) log n / n`. -/
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
