import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Ordinal.Arithmetic

universe u v

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/- Neighbours of `v` mapped to value `b` by `f`. -/
def NeighColored {β : Type*} (f : V → β)
    (v : V) (b : β) : Type u := ↥(G.neighborSet v ∩ f ⁻¹' {b})

/- A partial partition `f : V → Option Bool` is unfriendly at `x` when `x` is assigned
some colour `b` and has at least as many neighbours assigned the opposite colour
`!b` as assigned `b` -/
def UnfriendlyAt (f : V → Option Bool)
    (v : V) : Prop :=
  ∃ b : Bool, f v = some b ∧
    #(NeighColored G f v (some b)) ≤ #(NeighColored G f v (some (!b)))

/- The empty partial partition. -/
def emptyPartition (V : Type u) : V → Option Bool :=
  fun _ => none

/- A partial partition has finite domain when its set of assigned vertices is
finite. -/
def HasFiniteDomain (f : V → Option Bool) : Prop :=
  {v : V | f v ≠ none}.Finite

/-- A partial partition is total when every vertex is assigned a side. -/
def IsPartition (f : V → Option Bool) : Prop :=
  ∀ v : V, f v ≠ none

/-- `g` extends `f` when all assignments already made by `f` are preserved. -/
def Extends (f g : V → Option Bool) : Prop :=
  ∀ v b, f v = some b → g v = some b

/-- A partial partition is an unfriendly partition when it is total and
unfriendly at every vertex.  It reuses the single top-level `UnfriendlyAt`
(a partial partition is already a `V → Option Bool`). -/
def IsUnfriendlyPartition (f : V → Option Bool) : Prop :=
  ∀ x : V, UnfriendlyAt G f x

/-! ## The `r`-partitioning game -/

/- A legal response by Partitioner from position `f` to the challenged
vertex `v`: a finite partial partition `g` extending `f` which is unfriendly at `v` -/
def IsLegalResponse (f g : V → Option Bool) (v : V) : Prop :=
  Extends f g ∧ HasFiniteDomain g ∧ UnfriendlyAt G g v

/-  Partitioner has a winning strategy in the partitioning game from position
`(f, α)`. Defined inductively over `α` -/
def PartitionerWins (f : V → Option Bool)
  (α : Ordinal.{v}) : Prop :=
  ∀ v : V, ∀ β : Ordinal.{v}, β < α →
    ∃ g : V → Option Bool,
      IsLegalResponse G f g v ∧ PartitionerWins g β
termination_by α

/-- A winning position stays winning when the clock is lowered. -/
theorem PartitionerWins.mono {G : SimpleGraph V}
    {f : V → Option Bool} {α β : Ordinal.{v}}
    (hle : β ≤ α) (h : PartitionerWins G f α) :
    PartitionerWins G f β := by
  rw [PartitionerWins] at h ⊢
  intro v gamma hgamma
  exact h v gamma (lt_of_lt_of_le hgamma hle)

variable {V : Type u} [Countable V] (G : SimpleGraph V)

/-- The Scaled Unfriendly Partition Conjecture: for every ordinal `rho`,
Partitioner has a winning strategy in the `rho`-partitioning game on every
countable graph. -/
def UnfriendlyPartGameConj : Prop :=
  ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r
