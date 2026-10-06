/-
Prove-or-disprove companion — DISPROVE polarity for P061 (Seymour's exact
edge-colouring conjecture for planar multigraphs).

`P061` (in `P061.lean`) and `P061_disprove` (below) form a polarity pair in
the prove-or-disprove evaluation format: a model answers the problem by
giving a sorry-free proof of either one.

The conjecture is OPEN for every `d ≥ 9`; the cases `d ≤ 8` are theorems
(Four Colour Theorem at `d = 3` via Tait, Guenin for `d = 4, 5`,
Dvořák–Kawarabayashi–Král' for `d = 6`, and
Chudnovsky–Edwards–Kawarabayashi–Seymour for `d = 7, 8`), so a disproof
must exhibit, for some `d ≥ 9`, a `d`-regular oddly `d`-edge-connected
planar loopless multigraph that is not `d`-edge-colourable.  Note that
without planarity the Petersen graph refutes the analogous statement at
`d = 3`, so any counterexample must exploit high multiplicity in an
essential way — planar multigraph structure is heavily constrained by the
known cases.

Evaluation note: a submitted proof of either polarity must be type-checked
in isolation from the other polarity's `sorry` (a `sorry`-ed theorem acts
as an axiom).
-/
import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.EdgeColoring

open Multigraph

universe u v

/-- Disproof polarity of Seymour's exact conjecture: some `d`-regular oddly
`d`-edge-connected planar loopless multigraph is not `d`-edge-colourable. -/
theorem P061_disprove :
    ¬ ∀ (d : ℕ) (V : Type u) (E : Type v) [Fintype V] [Fintype E]
        [DecidableEq V] (M : Multigraph V E),
        (∀ e, ¬M.IsLoop e) → M.IsRegular d → M.OddlyEdgeConnected d →
          M.IsPlanar → M.EdgeColorable d := by
  sorry
