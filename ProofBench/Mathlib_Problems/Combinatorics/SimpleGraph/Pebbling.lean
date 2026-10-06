import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Order.Lattice.Nat

namespace SimpleGraph.Pebbling

variable {V : Type*} [DecidableEq V]

/-- A legal pebbling move removes two pebbles at one vertex and adds one at
an adjacent vertex; `c` is the unchanged remainder of the configuration. -/
def Step (G : SimpleGraph V) (a b : V → ℕ) : Prop :=
  ∃ (u v : V) (c : V → ℕ), G.Adj u v ∧ a = c + Pi.single u 2 ∧ b = c + Pi.single v 1

/-- A configuration can place a pebble at the prescribed root by finitely
many legal moves, including the empty sequence. -/
def Solvable (G : SimpleGraph V) (a : V → ℕ) (r : V) : Prop :=
  ∃ b, Relation.ReflTransGen (Step G) a b ∧ 1 ≤ b r

variable [Fintype V]

/-- Every configuration of at least `n` pebbles can reach every root. -/
def UniversalSolvable (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ a : V → ℕ, n ≤ ∑ v, a v → ∀ r, Solvable G a r

/-- The least universal pebbling threshold. For finite connected graphs
the defining set is nonempty; it is zero if no threshold exists. -/
noncomputable def pebblingNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | UniversalSolvable G n}

end SimpleGraph.Pebbling
