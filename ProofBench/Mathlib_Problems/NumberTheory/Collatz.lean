import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Logic.Function.Iterate

/-- One step of the Collatz map: an even number is halved, an odd `n` is sent to
`3 n + 1`. -/
def collatzStep (n : ℕ) : ℕ := if Even n then n / 2 else 3 * n + 1

/-- `n` reaches `1` under iteration of the Collatz map. -/
def CollatzReachesOne (n : ℕ) : Prop := ∃ k, collatzStep^[k] n = 1
