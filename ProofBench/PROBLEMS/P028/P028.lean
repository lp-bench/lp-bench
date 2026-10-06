import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic


/-! ###########################################################################
    A TUTTE-TYPE CANONICAL DECOMPOSITION OF 3- AND 4-CONNECTED GRAPHS
    ###########################################################################        -/
universe u

variable {V : Type u} [DecidableEq V]

/-! §1  Mixed separations -/

structure MixedSep (V : Type u) [DecidableEq V] where
  A : Finset V
  B : Finset V

namespace MixedSep

variable (s t : MixedSep V)

def vertSep : Finset V := s.A ∩ s.B
variable [Fintype V] in
def CoversAll : Prop := s.A ∪ s.B = Finset.univ
def IsProper : Prop := (s.A \ s.B).Nonempty ∧ (s.B \ s.A).Nonempty
def flip : MixedSep V := ⟨s.B, s.A⟩

protected def le (s t : MixedSep V) : Prop := s.A ⊆ t.A ∧ t.B ⊆ s.B
instance : LE (MixedSep V) := ⟨MixedSep.le⟩
theorem le_def : s ≤ t ↔ s.A ⊆ t.A ∧ t.B ⊆ s.B := Iff.rfl

theorem flip_A : s.flip.A = s.B := rfl
theorem flip_B : s.flip.B = s.A := rfl
theorem flip_flip : s.flip.flip = s := rfl

theorem vertSep_flip : s.flip.vertSep = s.vertSep := by
  simp [vertSep, flip, Finset.inter_comm]

theorem le_refl' (s : MixedSep V) : s ≤ s := ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

theorem le_trans' {s t u : MixedSep V} (h₁ : s ≤ t) (h₂ : t ≤ u) : s ≤ u :=
  ⟨Finset.Subset.trans h₁.1 h₂.1, Finset.Subset.trans h₂.2 h₁.2⟩

theorem le_antisymm' {s t : MixedSep V} (h₁ : s ≤ t) (h₂ : t ≤ s) : s = t := by
  obtain ⟨sA, sB⟩ := s
  obtain ⟨tA, tB⟩ := t
  have hA : sA = tA := Finset.Subset.antisymm h₁.1 h₂.1
  have hB : sB = tB := Finset.Subset.antisymm h₂.2 h₁.2
  simp_all

instance : PartialOrder (MixedSep V) where
  le := MixedSep.le
  le_refl := le_refl'
  le_trans := fun _ _ _ => le_trans'
  le_antisymm := fun _ _ => le_antisymm'

def Nested (s t : MixedSep V) : Prop :=
  s ≤ t ∨ t ≤ s ∨ s ≤ t.flip ∨ t.flip ≤ s

def Cross (s t : MixedSep V) : Prop := ¬ Nested s t
theorem cross_def : Cross s t ↔ ¬ Nested s t := Iff.rfl

theorem nested_self (s : MixedSep V) : Nested s s := Or.inl (le_refl' s)

theorem not_cross_self (s : MixedSep V) : ¬ Cross s s := by
  simp [Cross, nested_self]

theorem nested_symm {s t : MixedSep V} (h : Nested s t) : Nested t s := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))

theorem cross_symm {s t : MixedSep V} (h : Cross s t) : Cross t s :=
  fun hn => h (nested_symm hn)

end MixedSep

/-! §2  Order with edges -/

structure MixedSepWithOrder (V : Type u) [DecidableEq V] where
  ms : MixedSep V
  edgePart : ℕ

namespace MixedSepWithOrder
def order (o : MixedSepWithOrder V) : ℕ := o.ms.vertSep.card + o.edgePart
theorem order_def (o : MixedSepWithOrder V) :
    o.order = o.ms.vertSep.card + o.edgePart := rfl
end MixedSepWithOrder

variable [Fintype V]

noncomputable def edgeSepCard (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : MixedSep V) : ℕ :=
  (Finset.univ.filter
    (fun e : V × V => G.Adj e.1 e.2 ∧ e.1 ∈ s.A \ s.B ∧ e.2 ∈ s.B \ s.A)).card

noncomputable def sepOrder (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : MixedSep V) : ℕ :=
  s.vertSep.card + edgeSepCard G s

/-! §3  Degree- and matching-conditions -/

def DegreeCondition (G : SimpleGraph V) [DecidableRel G.Adj] (s : MixedSep V) :
    Prop :=
  ∀ v ∈ s.vertSep,
    2 ≤ (G.neighborFinset v ∩ (s.A \ s.B)).card ∧
    2 ≤ (G.neighborFinset v ∩ (s.B \ s.A)).card

def MatchingCondition (G : SimpleGraph V) [DecidableRel G.Adj] (s : MixedSep V) :
    Prop :=
  ∀ a₁ b₁ a₂ b₂ : V,
    (G.Adj a₁ b₁ ∧ a₁ ∈ s.A \ s.B ∧ b₁ ∈ s.B \ s.A) →
    (G.Adj a₂ b₂ ∧ a₂ ∈ s.A \ s.B ∧ b₂ ∈ s.B \ s.A) →
    (a₁ = a₂ ∨ b₁ = b₂) → (a₁ = a₂ ∧ b₁ = b₂)

/-! §4  Tetra- and strict tri-separations -/

structure TetraSep (G : SimpleGraph V) [DecidableRel G.Adj] where
  ms : MixedSep V
  hCovers   : ms.CoversAll
  hProper   : ms.IsProper
  hOrder    : sepOrder G ms = 4
  hDegree   : DegreeCondition G ms
  hMatching : MatchingCondition G ms

structure StrictTriSep (G : SimpleGraph V) [DecidableRel G.Adj] where
  ms : MixedSep V
  hCovers   : ms.CoversAll
  hProper   : ms.IsProper
  hOrder    : sepOrder G ms = 3
  hDegree   : DegreeCondition G ms
  hMatching : MatchingCondition G ms

namespace TetraSep
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def TotallyNested (ts : TetraSep G) : Prop :=
  ∀ ts' : TetraSep G, MixedSep.Nested ts.ms ts'.ms

theorem totallyNested_iff (ts : TetraSep G) :
    ts.TotallyNested ↔ ∀ ts' : TetraSep G, ¬ MixedSep.Cross ts.ms ts'.ms := by
  unfold TotallyNested MixedSep.Cross
  constructor
  · intro h ts'; simpa using h ts'
  · intro h ts'; have := h ts'; simpa using this

end TetraSep

namespace StrictTriSep
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def TotallyNested (ts : StrictTriSep G) : Prop :=
  ∀ ts' : StrictTriSep G, MixedSep.Nested ts.ms ts'.ms

end StrictTriSep

def vertexCentre (s t : MixedSep V) : Finset V := s.vertSep ∩ t.vertSep

omit [Fintype V] in
theorem vertexCentre_comm (s t : MixedSep V) :
    vertexCentre s t = vertexCentre t s := by
  simp [vertexCentre, Finset.inter_comm]

/-! §5  Connectivity -/

namespace SimpleGraph

def KConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (fun v => v ∉ S)).Connected

def QuasiSucc (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.KConnected k ∧
    ∀ A B : Finset V,
      A ∪ B = Finset.univ → (A \ B).Nonempty → (B \ A).Nonempty →
      (A ∩ B).card = k → (A \ B).card = 1 ∨ (B \ A).card = 1

def Quasi5Connected (G : SimpleGraph V) : Prop := G.QuasiSucc 4
def Quasi4Connected (G : SimpleGraph V) : Prop := G.QuasiSucc 3

theorem QuasiSucc.kConnected {G : SimpleGraph V} {k : ℕ}
    (h : G.QuasiSucc k) : G.KConnected k := h.1

end SimpleGraph

/-! §6  Torso types -/

inductive TorsoType : Type where
  | quasi5Connected        : TorsoType
  | cycleOfSmallTorsos     : TorsoType
  | generalisedDoubleWheel : TorsoType
  | thickenedK4m           : ℕ → TorsoType
  | sprinkledK4m           : ℕ → TorsoType
deriving DecidableEq, Repr

inductive TorsoType3 : Type where
  | quasi4Connected  : TorsoType3
  | generalisedWheel : TorsoType3
  | thickenedK3m     : ℕ → TorsoType3
  | sprinkledK3m     : ℕ → TorsoType3
deriving DecidableEq, Repr

/-! §7  Crossing-case enumeration -/

inductive CrossingCase : Type where
  | linksZeroCentreFour : CrossingCase
  | linksOneCentreTwo   : CrossingCase
  | linksTwoCentreZero  : CrossingCase
deriving DecidableEq, Repr

def CrossingCase.centreSize : CrossingCase → ℕ
  | .linksZeroCentreFour => 4
  | .linksOneCentreTwo   => 2
  | .linksTwoCentreZero  => 0

theorem CrossingCase.centreSize_mem (c : CrossingCase) :
    c.centreSize = 0 ∨ c.centreSize = 2 ∨ c.centreSize = 4 := by
  cases c <;> simp [CrossingCase.centreSize]

def CrossingLemmaConclusion {G : SimpleGraph V} [DecidableRel G.Adj]
    (ts₁ ts₂ : TetraSep G) : Prop :=
  ∃ c : CrossingCase, (vertexCentre ts₁.ms ts₂.ms).card = c.centreSize

theorem vertexCentre_card_mem
    {G : SimpleGraph V} [DecidableRel G.Adj] {ts₁ ts₂ : TetraSep G}
    (h : CrossingLemmaConclusion ts₁ ts₂) :
    (vertexCentre ts₁.ms ts₂.ms).card = 0 ∨
    (vertexCentre ts₁.ms ts₂.ms).card = 2 ∨
    (vertexCentre ts₁.ms ts₂.ms).card = 4 := by
  obtain ⟨c, hc⟩ := h
  rw [hc]
  exact c.centreSize_mem

/-! §8  Reduction conditions (Key Lemma 5.10) -/

namespace MixedSep
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def lowDegLeftCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : MixedSep V) : ℕ :=
  (s.vertSep.filter
    (fun v => (G.neighborFinset v ∩ (s.A \ s.B)).card ≤ 1)).card

structure LRConditions (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : MixedSep V) : Prop where
  cond_i   : 2 ≤ (s.A \ s.B).card
  cond_ii  : 2 - (s.B \ s.A).card ≤ lowDegLeftCount G s
  cond_iii : 2 ≤ (s.B \ s.A).card ∨ edgeSepCard G s ≤ 1

end MixedSep

/-! §9  External 5-connectivity (Key Lemma 6.16) -/

namespace TetraSep
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def ExternallyLinkedPair (ts : TetraSep G) (x y : V) : Prop :=
  G.Adj x y ∨ ∃ w ∈ (Finset.univ \ ts.ms.vertSep), G.Adj x w ∧ G.Adj w y

def HalfConnected (ts : TetraSep G) : Prop :=
  (G.induce (fun v => v ∈ ts.ms.A \ ts.ms.B)).Connected ∨
  (G.induce (fun v => v ∈ ts.ms.B \ ts.ms.A)).Connected

def ThreeLinkedSpec (ts : TetraSep G) : Prop :=
  ∀ x ∈ ts.ms.vertSep, ∀ y ∈ ts.ms.vertSep, x ≠ y → ts.ExternallyLinkedPair x y

def PotterLinkedSpec (ts : TetraSep G) (h : V) : Prop :=
  ∀ x ∈ ts.ms.vertSep, ∀ y ∈ ts.ms.vertSep,
    x ≠ y → x ≠ h → y ≠ h → ts.ExternallyLinkedPair x y

def PotterLinkedSpecs (ts : TetraSep G) : Prop :=
  ∀ h ∈ ts.ms.vertSep, ts.PotterLinkedSpec h

def ExternallyFiveConnected (ts : TetraSep G) : Prop :=
  ts.HalfConnected ∧ ts.ThreeLinkedSpec ∧ ts.PotterLinkedSpecs

def KeyLemma616Statement (ts : TetraSep G) : Prop :=
  ts.TotallyNested ↔ ts.ExternallyFiveConnected

theorem ExternallyFiveConnected.halfConnected {ts : TetraSep G}
    (h : ts.ExternallyFiveConnected) : ts.HalfConnected := h.1

theorem ExternallyFiveConnected.threeLinked {ts : TetraSep G}
    (h : ts.ExternallyFiveConnected) : ts.ThreeLinkedSpec := h.2.1

theorem ExternallyFiveConnected.potterLinked {ts : TetraSep G}
    (h : ts.ExternallyFiveConnected) : ts.PotterLinkedSpecs := h.2.2

end TetraSep

/-! §10  Apex construction -/

def apexGraph (G : SimpleGraph V) (α : V) : SimpleGraph V where
  Adj u v := G.Adj u v ∨ (u = α ∧ v ≠ α) ∨ (v = α ∧ u ≠ α)
  symm := ⟨by
    intro u v h
    rcases h with hg | ⟨rfl, hv⟩ | ⟨rfl, hu⟩
    · exact Or.inl hg.symm
    · exact Or.inr (Or.inr ⟨rfl, hv⟩)
    · exact Or.inr (Or.inl ⟨rfl, hu⟩)⟩
  loopless := ⟨by
    intro v h
    rcases h with hg | ⟨rfl, hv⟩ | ⟨rfl, hv⟩
    · exact G.loopless.irrefl v hg
    · exact hv rfl
    · exact hv rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem apexGraph_adj_apex (G : SimpleGraph V) (α : V) {v : V} (h : v ≠ α) :
    (apexGraph G α).Adj α v := Or.inr (Or.inl ⟨rfl, h⟩)

omit [Fintype V] [DecidableEq V] in
theorem apexGraph_adj_of_adj (G : SimpleGraph V) (α : V) {u v : V}
    (h : G.Adj u v) : (apexGraph G α).Adj u v := Or.inl h

/-! §11  Mixed-tree-decompositions, torsos, and Main Theorem 1 -/

/-- A mixed-tree-decomposition of `G`.

This includes the missing theorem-level data:
* the decomposition graph is a genuine tree;
* every tree edge induces a proper mixed separation;
* every tree-edge separation is a tetra-separation;
* the induced tetra-separations are exactly those coming from tree edges.
-/
structure MixedTreeDecomp (G : SimpleGraph V) (T : Type u)
    [Fintype T] [DecidableEq T] [DecidableRel G.Adj] where
  tree : SimpleGraph T
  hTree : tree.IsTree
  bag : T → Finset V

  /-- (M1) every vertex lies in some bag. -/
  hM1 : ∀ v : V, ∃ t : T, v ∈ bag t

  /-- (M2) the bags containing a fixed vertex induce a connected subtree. -/
  hM2 : ∀ v : V, (tree.induce (fun t => v ∈ bag t)).Connected

  /-- The mixed separation induced by a tree edge. -/
  sepOfAdj : ∀ ⦃t u : T⦄, tree.Adj t u → MixedSep V

  /-- Every decomposition separation is proper. -/
  sepOfAdj_proper :
    ∀ ⦃t u : T⦄ (h : tree.Adj t u), (sepOfAdj h).IsProper

  /-- Every decomposition separation is a tetra-separation. -/
  sepOfAdj_tetra :
    ∀ ⦃t u : T⦄ (h : tree.Adj t u),
      ∃ ts : TetraSep G, ts.ms = sepOfAdj h

  /-- Tetra-separations induced by this decomposition. -/
  inducedTetraSep : TetraSep G → Prop

  /-- The induced tetra-separations are exactly those coming from tree edges. -/
  induced_iff_tree_edge :
    ∀ ts : TetraSep G,
      inducedTetraSep ts ↔
        ∃ (t u : T) (h : tree.Adj t u), ts.ms = sepOfAdj h

/-- The decomposition uses exactly the totally-nested tetra-separations. -/
def UsesExactlyTotallyNested
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) : Prop :=
  ∀ ts : TetraSep G,
    D.inducedTetraSep ts ↔ TetraSep.TotallyNested ts

/-- Properness of all separations induced by tree edges. -/
def DecompSeparationsProper
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) : Prop :=
  ∀ ⦃t u : T⦄ (h : D.tree.Adj t u),
    (D.sepOfAdj h).IsProper

/-! ## Torsos -/

/-- Adhesion between adjacent decomposition nodes. -/
def Adhesion
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) (t u : T) : Finset V :=
  D.bag t ∩ D.bag u

/-- Two vertices of a bag lie together in an adhesion with a neighbouring bag. -/
def InCommonAdhesion
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) (t : T) (x y : V) : Prop :=
  ∃ u : T,
    D.tree.Adj t u ∧
    x ∈ Adhesion D t u ∧
    y ∈ Adhesion D t u

/-- Torso adjacency: original graph edges plus virtual adhesion edges. -/
def TorsoAdj
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) (t : T) (x y : V) : Prop :=
  x ∈ D.bag t ∧
  y ∈ D.bag t ∧
  x ≠ y ∧
  (G.Adj x y ∨ InCommonAdhesion D t x y)

/-- The torso graph at a decomposition node. -/
def TorsoGraph
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) (t : T) : SimpleGraph V where
  Adj := TorsoAdj D t
  symm := ⟨by
    intro x y h
    rcases h with ⟨hx, hy, hxy, hEdge⟩
    refine ⟨hy, hx, ?_, ?_⟩
    · intro hyx
      exact hxy hyx.symm
    · rcases hEdge with hG | hVirt
      · exact Or.inl hG.symm
      · rcases hVirt with ⟨u, htu, hxA, hyA⟩
        exact Or.inr ⟨u, htu, hyA, hxA⟩⟩
  loopless := ⟨by
    intro x h
    exact h.2.2.1 rfl⟩

/-- A torso is the completed bag graph at node `t`. -/
structure Torso
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) (t : T) where
  graph : SimpleGraph V
  graph_eq : graph = TorsoGraph D t
  vertexSet : Finset V
  vertexSet_eq : vertexSet = D.bag t

/-! ## Torso outcome specifications -/

def CompleteBipartiteOn
    (G : SimpleGraph V) (bag L R : Finset V) (a b : ℕ) : Prop :=
  L.card = a ∧
  R.card = b ∧
  L ⊆ bag ∧
  R ⊆ bag ∧
  L ∩ R = ∅ ∧
  ∀ l ∈ L, ∀ r ∈ R, G.Adj l r

def CycleSmallTorsoSpec
    (G : SimpleGraph V) (bag : Finset V) : Prop :=
  ∃ pieces : Finset (Finset V),
    pieces.Nonempty ∧
    (∀ P ∈ pieces,
      P ⊆ bag ∧
      3 ≤ P.card ∧
      P.card ≤ 5 ∧
      (G.induce (fun v => v ∈ P)).Connected) ∧
    ∀ v ∈ bag, ∃ P ∈ pieces, v ∈ P

def GeneralisedDoubleWheelSpec
    (G : SimpleGraph V) (bag : Finset V) : Prop :=
  ∃ C : Finset V,
    C.card = 2 ∧
    C ⊆ bag ∧
    ∀ c ∈ C, ∀ v ∈ bag, v ∉ C → G.Adj c v

def ThickenedK4mSpec
    (G : SimpleGraph V) (bag : Finset V) (m : ℕ) : Prop :=
  ∃ L R : Finset V,
    CompleteBipartiteOn G bag L R 4 m

def SprinkledK4mEntireGraphSpec
    (G : SimpleGraph V) (m : ℕ) : Prop :=
  4 ≤ m ∧
  ∃ L R : Finset V,
    CompleteBipartiteOn G Finset.univ L R 4 m

/-- The assigned torso type is genuinely witnessed by the actual torso graph. -/
def TorsoTypeCorrect
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) (t : T) (τ : Torso G D t) :
    TorsoType → Prop
  | .quasi5Connected =>
      τ.graph.Quasi5Connected
  | .cycleOfSmallTorsos =>
      CycleSmallTorsoSpec τ.graph τ.vertexSet
  | .generalisedDoubleWheel =>
      GeneralisedDoubleWheelSpec τ.graph τ.vertexSet
  | .thickenedK4m m =>
      ThickenedK4mSpec τ.graph τ.vertexSet m
  | .sprinkledK4m m =>
      SprinkledK4mEntireGraphSpec G m

/-- Canonicity/uniqueness: another decomposition using exactly the same
totally-nested tetra-separations is isomorphic as a decomposition tree and has
corresponding equal bags. -/
def CanonicalDecomp
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : Type u} [Fintype T] [DecidableEq T]
    (D : MixedTreeDecomp G T) : Prop :=
  ∀ (T' : Type u) [Fintype T'] [DecidableEq T']
    (D' : MixedTreeDecomp G T'),
    UsesExactlyTotallyNested D' →
    ∃ e : T ≃ T',
      (∀ t : T, D.bag t = D'.bag (e t)) ∧
      (∀ t u : T, D.tree.Adj t u ↔ D'.tree.Adj (e t) (e u))


/-! ###########################################################################
    §12  Main Theorem 1
    #########################################################################-/

/- A torso-classification function assigns each tree node a `TorsoType`.
    A real proof of Theorem 1 must produce such a function AND a witness that
    each assignment is correct.  We expose the *shape* of that obligation. -/
/- Theorem 1: Main decomposition theorem for 4-connected graphs.
    The statement asserts existence of a canonical decomposition with correct
    torso types. -/

def MainTheorem1Statement (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.KConnected 4 →
    ∃ (T : Type u) (instT : Fintype T) (instEq : DecidableEq T),
      letI : Fintype T := instT
      letI : DecidableEq T := instEq
      ∃ (decomp : MixedTreeDecomp G T)
        (torso : ∀ t : T, Torso G decomp t)
        (torsoType : T → TorsoType),
        UsesExactlyTotallyNested decomp ∧
        DecompSeparationsProper decomp ∧
        (∀ t : T, TorsoTypeCorrect decomp t (torso t) (torsoType t)) ∧
        CanonicalDecomp decomp
theorem P028 (G : SimpleGraph V) [DecidableRel G.Adj] :
    MainTheorem1Statement G := by
  sorry
