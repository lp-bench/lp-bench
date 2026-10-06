import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Decomposition
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Cycle decompositions for the Kurkofka–Planken connectivity theorem

Kurkofka–Planken (*A characterisation of all vertex-transitive finite graphs of connectivity < 5*)
introduce graph-decompositions whose decomposition graph "may take the form of an arbitrary graph,
such as a cycle, in which case we speak of a *cycle-decomposition* [9]"; their reference [9] is the
Diestel–Jacobs–Knappe–Kurkofka paper *Canonical graph decompositions via coverings*, whose
graph-decomposition.

A cycle-decomposition is therefore **not a new structure**: it is `GraphDecomp G H` with the model
`H` taken to be the cycle `C_l = cycleGraph l`. This file makes that the definition and rebuilds the
adhesion/torso/bag vocabulary and the named "cycle of `X`-bags" classes (Definition 2.3) on top of
it. -/

open SimpleGraph

universe u v

namespace Cyclic_Decomposition

variable {V : Type u}

/-- Graph isomorphism without finiteness assumptions. -/
def GraphIso {A : Type u} {B : Type v}
    (G : SimpleGraph A) (H : SimpleGraph B) : Prop :=
  exists e : Equiv A B, forall x y : A, G.Adj x y <-> H.Adj (e x) (e y)

/-- A set has exactly two elements, stated without choosing decidable equality. -/
def SetHasTwo (S : Set V) : Prop :=
  exists a b : V, a ≠ b /\ S = ({a, b} : Set V)

/-- `A` and `B` are the same unoriented edge of the decomposition cycle. -/
def SameCycleEdge {l : Nat} (i j k m : Fin l) : Prop :=
  (i = k /\ j = m) \/ (i = m /\ j = k)

/-- Two edges of the decomposition cycle share an endpoint. -/
def CycleEdgesIncident {l : Nat} (i j k m : Fin l) : Prop :=
  i = k ∨ i = m \/ j = k \/ j = m

/-- A **cycle-decomposition** of `G` of length `l` (Kurkofka–Planken): a Diestel
graph-decomposition (`GraphDecomp`, from `H_decomposition`) whose model graph is the cycle
`C_l = cycleGraph l`. It is literally the specialisation of `GraphDecomp` to a cyclic model — no
new axioms. Length bounds (`3 ≤ l`, etc.) are imposed by the Definition 2.3 classes below. -/
abbrev CycleDecomp (G : SimpleGraph V) (l : Nat) := GraphDecomp G (cycleGraph l)

namespace CycleDecomp

variable {G : SimpleGraph V} {l : Nat}

/-- The graph induced by the bag at the cycle node `i` (the part `G[V_i]`). -/
def bagGraph (O : CycleDecomp G l) (i : Fin l) :
    SimpleGraph {x : V // x ∈ O.bag i} :=
  G.induce (O.bag i)

/-- The adhesion set on the cycle edge `ij`, namely `V_i ∩ V_j`. -/
def adhesion (O : CycleDecomp G l) (i j : Fin l) : Set V :=
  O.bag i ∩ O.bag j

/-- Every cycle adhesion set has size two, as required in the paper's
cycle-decomposition terminology used before Definition 2.3. -/
def AdhesionsHaveSizeTwo (O : CycleDecomp G l) : Prop :=
  forall i j : Fin l, (cycleGraph l).Adj i j -> SetHasTwo (O.adhesion i j)

/-- Every pair of distinct adhesion sets is disjoint. -/
def PairwiseDisjointAdhesions (O : CycleDecomp G l) : Prop :=
  forall i j k m : Fin l,
    (cycleGraph l).Adj i j ->
    (cycleGraph l).Adj k m ->
    Not (SameCycleEdge i j k m) ->
      Disjoint (O.adhesion i j) (O.adhesion k m)

/-- Adhesions on non-consecutive cycle edges are disjoint. -/
def NonconsecutiveAdhesionsDisjoint (O : CycleDecomp G l) : Prop :=
  forall i j k m : Fin l,
    (cycleGraph l).Adj i j ->
    (cycleGraph l).Adj k m ->
    Not (CycleEdgesIncident i j k m) ->
      Disjoint (O.adhesion i j) (O.adhesion k m)

/-- An adhesion set is independent in `G`. -/
def AdhesionIndependent (O : CycleDecomp G l) (i j : Fin l) : Prop :=
  forall x y : V, x ∈ O.adhesion i j -> y ∈ O.adhesion i j -> Not (G.Adj x y)

/-- Every adhesion set along the cycle is independent. -/
def AdhesionsIndependent (O : CycleDecomp G l) : Prop :=
  forall i j : Fin l, (cycleGraph l).Adj i j -> O.AdhesionIndependent i j

/-- An adhesion set induces a `K_2`: it consists of two adjacent vertices. -/
def AdhesionInducesK2 (O : CycleDecomp G l) (i j : Fin l) : Prop :=
  SetHasTwo (O.adhesion i j) /\
    forall x y : V,
      x ∈ O.adhesion i j -> y ∈ O.adhesion i j -> x ≠ y -> G.Adj x y

/-- Every cycle adhesion set induces a `K_2`. -/
def AdhesionsInduceK2 (O : CycleDecomp G l) : Prop :=
  forall i j : Fin l, (cycleGraph l).Adj i j -> O.AdhesionInducesK2 i j

/-- The torso at node `i`: the bag graph plus clique edges inside each
adhesion set incident with `i`. -/
def torsoGraph (O : CycleDecomp G l) (i : Fin l) :
    SimpleGraph {x : V // x ∈ O.bag i} where
  Adj x y :=
    G.Adj (x : V) (y : V) \/
      exists j : Fin l,
        (cycleGraph l).Adj i j /\
          x ≠ y /\
          (x : V) ∈ O.adhesion i j /\
          (y : V) ∈ O.adhesion i j
  symm := ⟨by
    intro x y h
    cases h with
    | inl hxy =>
        exact Or.inl hxy.symm
    | inr htorso =>
        rcases htorso with ⟨j, hij, hne, hx, hy⟩
        exact Or.inr ⟨j, hij, Ne.symm hne, hy, hx⟩⟩
  loopless := ⟨by
    intro x h
    cases h with
    | inl hxx =>
        exact G.loopless.1 (x : V) hxx
    | inr htorso =>
        rcases htorso with ⟨_, _, hne, _, _⟩
        exact hne rfl⟩

/-- The bag at `i` is isomorphic to a model graph `X`. -/
def BagIs (O : CycleDecomp G l) (i : Fin l) {A : Type v}
    (X : SimpleGraph A) : Prop :=
  GraphIso (O.bagGraph i) X

/-- The torso at `i` is isomorphic to a model graph `X`. -/
def TorsoIs (O : CycleDecomp G l) (i : Fin l) {A : Type v}
    (X : SimpleGraph A) : Prop :=
  GraphIso (O.torsoGraph i) X

/-- `K_n` as a complete graph on `Fin n`. -/
def K (n : Nat) : SimpleGraph (Fin n) :=
  completeGraph (Fin n)

/-- The complete bipartite graph `K_{2,2}`, represented as `K_2 □ K_2`. -/
def K22 : SimpleGraph (Fin 2 × Fin 2) :=
  completeGraph (Fin 2) □ completeGraph (Fin 2)

/-- Bag predicate for `K_4` bags. -/
def IsK4Bag (O : CycleDecomp G l) (i : Fin l) : Prop :=
  O.BagIs i (K 4)

/-- Bag predicate for `C_4` bags. -/
def IsC4Bag (O : CycleDecomp G l) (i : Fin l) : Prop :=
  O.BagIs i (cycleGraph 4)

/-- Bag predicate for triangle bags. -/
def IsTriangleBag (O : CycleDecomp G l) (i : Fin l) : Prop :=
  O.BagIs i (K 3)

/-- Bag predicate for `K_{2,2}` bags. -/
def IsK22Bag (O : CycleDecomp G l) (i : Fin l) : Prop :=
  O.BagIs i K22

/-- Torso predicate for `K_4` torsos. -/
def IsK4Torso (O : CycleDecomp G l) (i : Fin l) : Prop :=
  O.TorsoIs i (K 4)

/-- Torso predicate for `C_4` torsos. -/
def IsC4Torso (O : CycleDecomp G l) (i : Fin l) : Prop :=
  O.TorsoIs i (cycleGraph 4)

end CycleDecomp

/-- Definition 2.3: cycle of `K_4` bags of length `l`. -/
def IsCycleOfK4Bags (G : SimpleGraph V) (l : Nat) : Prop :=
  exists O : CycleDecomp G l,
    4 <= l /\
      O.AdhesionsHaveSizeTwo /\
      O.PairwiseDisjointAdhesions /\
      forall i : Fin l, O.IsK4Bag i

/-- Definition 2.3: cycle alternating between `K_4` bags and `C_4` bags. -/
def IsCycleAlternatingK4C4 (G : SimpleGraph V) (l : Nat) : Prop :=
  l % 2 = 0 /\
    exists O : CycleDecomp G l,
      4 <= l /\
        O.AdhesionsHaveSizeTwo /\
        O.PairwiseDisjointAdhesions /\
        forall i : Fin l,
          (i.val % 2 = 0 /\ O.IsK4Bag i) \/
            (i.val % 2 = 1 /\ O.IsC4Bag i)

/-- Definition 2.3: cycle of triangle bags. -/
def IsCycleOfTriangleBags (G : SimpleGraph V) (l : Nat) : Prop :=
  exists O : CycleDecomp G l,
    6 <= l /\
      O.AdhesionsHaveSizeTwo /\
      O.NonconsecutiveAdhesionsDisjoint /\
      forall i : Fin l, O.IsTriangleBag i

/-- Definition 2.3: cycle alternating between `K_{2,2}` bags and `C_4` torsos. -/
def IsCycleAlternatingK22C4 (G : SimpleGraph V) (l : Nat) : Prop :=
  l % 2 = 0 /\
    exists O : CycleDecomp G l,
      6 <= l /\
        O.AdhesionsHaveSizeTwo /\
        O.AdhesionsIndependent /\
        O.PairwiseDisjointAdhesions /\
        forall i : Fin l,
          (i.val % 2 = 0 /\ O.IsK4Torso i /\ O.IsK22Bag i) \/
            (i.val % 2 = 1 /\ O.IsC4Torso i)

/-- Definition 2.3: cycle of `C_4` bags. -/
def IsCycleOfC4Bags (G : SimpleGraph V) (l : Nat) : Prop :=
  exists O : CycleDecomp G l,
    4 <= l /\
      O.AdhesionsInduceK2 /\
      O.PairwiseDisjointAdhesions /\
      forall i : Fin l, O.IsC4Bag i

/-- Definition 2.3: cycle of `K_{2,2}` bags. -/
def IsCycleOfK22Bags (G : SimpleGraph V) (l : Nat) : Prop :=
  exists O : CycleDecomp G l,
    3 <= l /\
      O.AdhesionsHaveSizeTwo /\
      O.PairwiseDisjointAdhesions /\
      (forall i : Fin l, O.IsK22Bag i) /\
      forall i : Fin l, O.IsK4Torso i

end Cyclic_Decomposition
