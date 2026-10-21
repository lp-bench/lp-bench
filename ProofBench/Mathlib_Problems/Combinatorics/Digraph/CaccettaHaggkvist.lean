import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Rotate

variable {V : Type*} (D : Digraph V)

/-- `c` lists a directed cycle of length `k` in `D`: `k` distinct vertices
`c 0, …, c (k - 1)`, each joined by an arc to the cyclically next one. -/
def Digraph.IsCycle {k : ℕ} (c : Fin k → V) : Prop :=
  Function.Injective c ∧ ∀ i, D.Adj (c i) (c (finRotate k i))

/-- The out-degree of `v`: the number of arcs leaving `v` (a loop counts). -/
noncomputable def Digraph.outDegree (v : V) : ℕ := {w | D.Adj v w}.ncard

/-- **The Caccetta–Häggkvist conjecture at minimum out-degree `r`**: every finite
nonempty digraph on `n` vertices in which every vertex has out-degree at least `r`
contains a directed cycle of length at most `⌈n / r⌉`. -/
def CaccettaHaggkvistFor (r : ℕ) : Prop :=
  ∀ {W : Type} [Fintype W] [Nonempty W] (D : Digraph W), (∀ v, r ≤ D.outDegree v) →
    ∃ k, 0 < k ∧ k ≤ Fintype.card W ⌈/⌉ r ∧ ∃ c : Fin k → W, D.IsCycle c
