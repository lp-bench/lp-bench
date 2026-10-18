/-
Copyright (c) 2026 ProofBench participants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ProofBench participants
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace TokenGraph

open Finset Matrix

/-- The configurations of `k` indistinguishable tokens on distinct vertices. -/
abbrev TokenSet (V : Type*) (k : ℕ) := {A : Finset V // A.card = k}

section TokenGraph

variable {V : Type*} [DecidableEq V]

/-- Two token configurations are adjacent when one token moves along an edge
to an unoccupied vertex. -/
def TokenAdj (G : SimpleGraph V) (k : ℕ) (A B : TokenSet V k) : Prop :=
  ∃ u v, G.Adj u v ∧ u ∈ A.1 ∧ v ∉ A.1 ∧ B.1 = insert v (A.1.erase u)

/-- The `k`-token graph of `G`. -/
def tokenGraph (G : SimpleGraph V) (k : ℕ) : SimpleGraph (TokenSet V k) where
  Adj := TokenAdj G k
  symm := ⟨by
    rintro A B ⟨u, v, huv, hu, hv, hB⟩
    refine ⟨v, u, huv.symm, ?_, ?_, ?_⟩
    · rw [hB]
      exact mem_insert_self v _
    · rw [hB]
      simpa only [mem_insert, not_or] using
        ⟨fun h ↦ hv (h ▸ hu), notMem_erase u A.1⟩
    · rw [hB, erase_insert (fun h ↦ hv (mem_of_mem_erase h)), insert_erase hu]⟩
  loopless := ⟨by
    rintro A ⟨u, v, _, _, hv, hA⟩
    exact hv (hA ▸ mem_insert_self v _)⟩

end TokenGraph

section Decidable

variable {V : Type*} [Fintype V] [DecidableEq V]

instance (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (tokenGraph G k).Adj := by
  unfold tokenGraph TokenAdj
  infer_instance

/-- The second-smallest Laplacian eigenvalue, with value zero for graphs on
fewer than two vertices. -/
noncomputable def algebraicConnectivity (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  if h : 1 < Fintype.card V then
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ (Fin.rev ⟨1, h⟩)
  else 0

end Decidable

end TokenGraph
