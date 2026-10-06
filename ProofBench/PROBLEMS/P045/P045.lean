import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace EssentialRainbowCycle

universe u v

variable {V : Type u} {Color : Type v} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The average degree `d(G) = 2|E(G)| / |V(G)|` of a finite simple graph. -/
noncomputable def averageDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (2 * (G.edgeFinset.card : ℝ)) / (Fintype.card V : ℝ)

/-- A proper edge-colouring: adjacent edges — adjacent vertices of the line
graph — receive distinct colours. -/
def IsProperEdgeColoring (chi : G.EdgeLabeling Color) : Prop :=
  ∀ e1 e2 : G.edgeSet, G.lineGraph.Adj e1 e2 → chi e1 ≠ chi e2

/-- The list of colours appearing along a walk, in walk order. -/
def edgeColorsOfWalk (chi : G.EdgeLabeling Color) {x y : V} (p : G.Walk x y) :
    List Color :=
  p.edges.attach.map fun e => chi ⟨e.1, p.edges_subset_edgeSet e.2⟩

/-- A rainbow cycle is a cycle whose edge colours are pairwise distinct. -/
def IsRainbowCycle (chi : G.EdgeLabeling Color) {x : V} (p : G.Walk x x) :
    Prop :=
  p.IsCycle ∧ (edgeColorsOfWalk chi p).Nodup

/-- The graph contains a rainbow cycle for the given edge-colouring. -/
def ContainsRainbowCycle (G : SimpleGraph V) [DecidableRel G.Adj]
    (chi : G.EdgeLabeling Color) : Prop :=
  ∃ x : V, ∃ p : G.Walk x x, IsRainbowCycle chi p

/-- The rainbow-cycle threshold statement for a threshold function `f`: some
constant multiple of `f n` on the average degree forces a rainbow cycle in
every properly edge-coloured graph on `n ≥ 3` vertices. -/
def RainbowCycleThreshold (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      {Color : Type v} (chi : G.EdgeLabeling Color),
        3 ≤ Fintype.card V →
        IsProperEdgeColoring (G := G) chi →
        C * f (Fintype.card V : ℝ) ≤ averageDegree G →
        ContainsRainbowCycle G chi

/-- **Theorem 1.1** of "Essentially tight bounds for rainbow cycles in proper
edge-colourings": there is an absolute constant `C > 0` such that every
properly edge-coloured graph on `n ≥ 3` vertices with average degree at least
`C · log n · log log n` contains a rainbow cycle. -/
theorem P045 : RainbowCycleThreshold.{u, v}
    (fun n => Real.log n * Real.log (Real.log n)) := by
  sorry

end EssentialRainbowCycle
