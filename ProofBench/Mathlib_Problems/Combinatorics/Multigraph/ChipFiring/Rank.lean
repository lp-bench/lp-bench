import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.ChipFiring
import ProofBench.Mathlib_Problems.Combinatorics.BrillNoether

/-- A divisor is winnable when its firing class contains an effective
representative. -/
def winnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ E : CFDiv G, effective E ∧ linear_equiv G D E

/-- The relation `rank(D) ≥ r`: after removing any effective divisor of degree
`r`, the resulting divisor is still winnable. This relational form follows
Mavani–Pflueger's Apache-2.0 `chip-firing-with-lean`. -/
def divisorRankAtLeast (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  ∀ A : CFDiv G, effective A → deg A = r → winnable G (D - A)

/-- The relation `rank(D) = r`, expressed without choosing an integer-valued
rank function. -/
def divisorRankEq (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  divisorRankAtLeast G D r ∧ ¬divisorRankAtLeast G D (r + 1)
