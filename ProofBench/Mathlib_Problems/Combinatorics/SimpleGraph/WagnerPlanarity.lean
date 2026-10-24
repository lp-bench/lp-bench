module

import Mathlib.Combinatorics.SimpleGraph.Basic
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Minor

@[expose] public section

open SimpleGraph Minor

universe u

variable {V : Type u}

/-- The complete graph `K₅`. -/
abbrev K5 := completeGraph (Fin 5)

/-- The complete bipartite graph `K₃,₃`. -/
abbrev K33 := completeBipartiteGraph (Fin 3) (Fin 3)

/-- Planarity defined through Wagner's theorem: a finite graph is planar when it has
neither `K₅` nor `K₃,₃` as a minor. -/
def SimpleGraph.IsWagnerPlanar [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (Minor K5 G) ∧ ¬ Nonempty (Minor K33 G)
