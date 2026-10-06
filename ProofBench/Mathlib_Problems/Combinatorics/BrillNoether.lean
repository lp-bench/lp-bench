import Mathlib.Data.Int.Basic

/-- The Brill--Noether number `ρ(g,r,d) = g - (r+1)(g-d+r)`. -/
def brillNoetherNumber (g r d : ℤ) : ℤ :=
  g - (r + 1) * (g - d + r)
