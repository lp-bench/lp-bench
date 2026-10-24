import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Ordinal.Arithmetic

universe u v

open scoped Cardinal

variable {V : Type u} (G : SimpleGraph V)

/-- The neighbours of `v` that `f` maps to the value `b`. -/
def NeighColored {β : Type*} (f : V → β)
    (v : V) (b : β) : Type u := ↥(G.neighborSet v ∩ f ⁻¹' {b})

/-- A partial partition `f : V → Option Bool` is unfriendly at `v` when `v` is assigned
some side `b` and has at least as many neighbours (as a cardinal) assigned the opposite
side `!b` as assigned `b`; unassigned neighbours do not count. -/
def UnfriendlyAt (f : V → Option Bool)
    (v : V) : Prop :=
  ∃ b : Bool, f v = some b ∧
    #(NeighColored G f v (some b)) ≤ #(NeighColored G f v (some (!b)))

/-- The empty partial partition: no vertex is assigned a side. -/
def emptyPartition (V : Type u) : V → Option Bool :=
  fun _ => none

/-- A partial partition has finite domain when its set of assigned vertices is
finite. -/
def HasFiniteDomain (f : V → Option Bool) : Prop :=
  {v : V | f v ≠ none}.Finite

/-- A partial partition is total when every vertex is assigned a side. -/
def IsPartition (f : V → Option Bool) : Prop :=
  ∀ v : V, f v ≠ none

/-- `g` extends `f` when all assignments already made by `f` are preserved. -/
def Extends (f g : V → Option Bool) : Prop :=
  ∀ v b, f v = some b → g v = some b

/-- An unfriendly partition: unfriendly at every vertex (which forces every vertex
to be assigned a side). -/
def IsUnfriendlyPartition (f : V → Option Bool) : Prop :=
  ∀ x : V, UnfriendlyAt G f x

/-- A legal response by Partitioner from position `f` to the challenged vertex `v`:
a finite partial partition `g` extending `f` that is unfriendly at `v`. -/
def IsLegalResponse (f g : V → Option Bool) (v : V) : Prop :=
  Extends f g ∧ HasFiniteDomain g ∧ UnfriendlyAt G g v

/-- Partitioner has a winning strategy in the partitioning game from position `(f, α)`:
for every vertex `v` and ordinal `β < α` named by Challenger there is a legal response `g`
from which Partitioner wins at `(g, β)`. Defined by well-founded recursion on `α`. -/
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

/-- The Scaled Unfriendly Partition Conjecture for `G`: for every ordinal `r`, Partitioner
has a winning strategy in the `r`-partitioning game on `G`, starting from the empty partial
partition. -/
def UnfriendlyPartGameConj : Prop :=
  ∀ r : Ordinal.{v}, PartitionerWins G (emptyPartition V) r
