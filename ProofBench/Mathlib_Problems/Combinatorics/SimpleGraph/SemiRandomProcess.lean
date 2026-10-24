import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory

noncomputable section

namespace PerfectMatchingSemiRandom

variable {V : Type*}

/-- The simple graph containing just the edge `u v`. When `u = v`, the loop is discarded, as in
passing from the multigraph of a play to its underlying simple graph. -/
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

/-- `G` is a subgraph of `addEdge G u v`. -/
theorem le_addEdge (G : SimpleGraph V) (u v : V) :
    G <= addEdge G u v :=
  le_sup_left

/-- The added edge lies in `addEdge G u v`. -/
theorem singleEdge_le_addEdge (G : SimpleGraph V) (u v : V) :
    singleEdge u v <= addEdge G u v :=
  le_sup_right

/-- A play of `T` rounds: the offered vertex and the response in each round. The response may
depend on the past and on the current offered vertex; that dependence belongs to the strategy
generating the play. -/
structure Play (V : Type*) (T : Nat) where
  offered : Fin T -> V
  response : Fin T -> V

instance playMeasurableSpace (V : Type*) (T : Nat) :
    MeasurableSpace (Play V T) := ⊤

/-- The underlying simple graph produced by all rounds of a play. -/
def Play.graph {T : Nat} (play : Play V T) : SimpleGraph V :=
  ⨆ t : Fin T, singleEdge (play.offered t) (play.response t)

/-- The edge of each round lies in the graph of the play. -/
theorem Play.singleEdge_le_graph {T : Nat} (play : Play V T) (t : Fin T) :
    singleEdge (play.offered t) (play.response t) <= play.graph := by
  exact le_iSup (fun i : Fin T =>
    singleEdge (play.offered i) (play.response i)) t

/-- A graph property is increasing if adding edges preserves it. -/
def IncreasingProperty (property : SimpleGraph V -> Prop) : Prop :=
  forall G H, G <= H -> property G -> property H

/-- The conjunction of two increasing properties is increasing. -/
theorem IncreasingProperty.trans
    {P Q : SimpleGraph V -> Prop}
    (hP : IncreasingProperty P)
    (hQ : IncreasingProperty Q) :
    IncreasingProperty fun G => P G /\ Q G := by
  intro G H hGH h
  exact ⟨hP G H hGH h.1, hQ G H hGH h.2⟩

/-- Probability of achieving a graph property under a law on realized plays. -/
def successProbability {T : Nat}
    (law : Measure (Play V T)) (property : SimpleGraph V -> Prop) : Real :=
  law.real {play | property play.graph}

end PerfectMatchingSemiRandom

end
