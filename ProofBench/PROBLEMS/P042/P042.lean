import Mathlib.NumberTheory.LSeries.RiemannZeta

/- ==============================================================================
P042 — The Riemann Hypothesis.

Every nontrivial zero of the Riemann zeta function has real part `1/2`.
The statement is Mathlib's own `RiemannHypothesis` (from
`Mathlib.NumberTheory.LSeries.RiemannZeta`): for every `s : ℂ` with
`riemannZeta s = 0` that is neither a trivial zero (`s = -2(n+1)`) nor the
point `s = 1`, the real part of `s` is `1/2`.

OPEN problem; the DISPROVE polarity lives in `P042_DISPROVE.lean`.
Upper/lower bound files in the P001 theorem-sandwich style are still to be
added (e.g. prime-counting consequences as LB, and the classical zero-free
strip results as UB).
============================================================================== -/

/-- **The Riemann Hypothesis**: every nontrivial zero of the Riemann zeta
function lies on the critical line `re s = 1/2`. -/
theorem P042 : RiemannHypothesis := by
  sorry
