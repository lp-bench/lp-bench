import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.RotationSystem

open Function

universe u v

namespace SimpleGraph

variable {V : Type u} {W : Type v} (H : SimpleGraph W) (G : SimpleGraph V)

/-- A graph covering map: a surjective graph homomorphism inducing a bijection
between the neighborhoods of each vertex and its image. -/
structure Cover where
  toHom : H →g G
  locallyBijective : ∀ w, Bijective (toHom.mapNeighborSet w)
  surjective : Surjective toHom

/-- A graph has a finite planar cover if it is covered by a finite graph with
a planar rotation system. -/
def HasFinitePlanarCover (G : SimpleGraph V) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    Nonempty (H.Cover G) ∧ H.IsGenusZero

/-- The complete multipartite graph with parts of sizes `1, 2, 2, 2`. -/
abbrev K1222 :=
  completeMultipartiteGraph (Fin.cases (Fin 1) fun _ : Fin 3 ↦ Fin 2)

end SimpleGraph
