module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.LineGraph

import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.Order.Category.Preord
import Mathlib.Algebra.Order.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pretransitive

public section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def VertexTransitive (G : SimpleGraph V) : Prop :=
   MulAction.IsPretransitive (G ≃g G) V

def ArcTransitive (G : SimpleGraph V) : Prop :=
  ∀ d₁ d₂ : G.Dart, ∃ φ : G ≃g G, φ.toHom.mapDart d₁ = d₂
