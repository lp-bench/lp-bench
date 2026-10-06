import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Real.Basic

namespace SimpleGraph

variable {V : Type*}

/-- The number of connected components remaining after deleting the vertex
set `S`. -/
noncomputable def numComponentsOutside (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (↑S : Set V)ᶜ).ConnectedComponent

/-- `G` is `t`-tough: every vertex set whose deletion disconnects the graph
(leaves at least two components) must contain at least `t` vertices per
component created. -/
def IsTough (t : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, 2 ≤ G.numComponentsOutside S →
    t * G.numComponentsOutside S ≤ S.card

/-- Larger toughness is a stronger requirement. -/
theorem IsTough.mono {G : SimpleGraph V} {s t : ℝ} (hst : s ≤ t)
    (h : G.IsTough t) : G.IsTough s := fun S hS =>
  le_trans (mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg _)) (h S hS)

end SimpleGraph
