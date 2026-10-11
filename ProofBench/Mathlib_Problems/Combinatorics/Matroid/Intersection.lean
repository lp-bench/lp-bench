import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Closure

namespace Matroid

variable {α : Type*}

/-- A matroid is *tame* if every circuit meets every cocircuit in a finite set. -/
def Tame (M : Matroid α) : Prop :=
  ∀ ⦃C K : Set α⦄, M.IsCircuit C → M.IsCocircuit K → (C ∩ K).Finite

/-- Matroids `M` and `N` on a common ground set `E` *satisfy intersection*: for some disjoint
`J₀` and `J₁`, the set `J₀ ∪ J₁` is independent in both and `cl_M J₀ ∪ cl_N J₁ = E`. -/
def SatisfiesIntersection (M N : Matroid α) : Prop :=
  ∃ J₀ J₁ : Set α, Disjoint J₀ J₁ ∧ M.Indep (J₀ ∪ J₁) ∧ N.Indep (J₀ ∪ J₁) ∧
    M.closure J₀ ∪ N.closure J₁ = M.E

end Matroid
