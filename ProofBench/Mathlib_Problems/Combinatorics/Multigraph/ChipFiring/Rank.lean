import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring
import ProofBench.Mathlib_Problems.Combinatorics.BrillNoether

/-!
This minimal rank API follows the relational definition in Dhyey Mavani and
Nathan Pflueger's Apache-2.0-licensed `chip-firing-with-lean` development.  It
contains exactly the additional definitions needed to state the Brill--Noether
existence problem; properties of the relation remain in the hidden library.
-/

/-- A divisor is winnable when its firing class contains an effective
representative. -/
def winnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ E : CFDiv G, effective E ∧ linear_equiv G D E

/-- The relation `rank(D) ≥ r`: after removing any effective divisor of degree
`r`, the resulting divisor is still winnable. -/
def divisorRankAtLeast (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  ∀ A : CFDiv G, effective A → deg A = r → winnable G (D - A)

/-- The relation `rank(D) = r`, expressed without choosing an integer-valued
rank function. -/
def divisorRankEq (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  divisorRankAtLeast G D r ∧ ¬divisorRankAtLeast G D (r + 1)
