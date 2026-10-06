import ProofBench.Mathlib_Problems.Combinatorics.MetricGraph.Divisor
import ProofBench.Mathlib_Problems.Combinatorics.BrillNoether

/-- A metric-graph divisor is winnable when its linear-equivalence class
contains an effective representative. -/
def metricWinnable (G : MetricGraph) (D : MetricDiv G) : Prop :=
  ∃ E : MetricDiv G, metricEffective E ∧ metricLinearEquiv G D E

/-- The relation `rank(D) ≥ r` for a divisor on a metric graph. -/
def metricDivisorRankAtLeast (G : MetricGraph) (D : MetricDiv G) (r : ℤ) : Prop :=
  ∀ A : MetricDiv G, metricEffective A → metricDegree A = r →
    metricWinnable G (D - A)

/-- The relation `rank(D) = r` for a divisor on a metric graph. -/
def metricDivisorRankEq (G : MetricGraph) (D : MetricDiv G) (r : ℤ) : Prop :=
  metricDivisorRankAtLeast G D r ∧
    ¬metricDivisorRankAtLeast G D (r + 1)
