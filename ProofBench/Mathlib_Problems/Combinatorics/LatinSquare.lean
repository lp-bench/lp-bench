import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Function

/-- A Latin square of order `n`: an `n × n` array of symbols from `Fin n` with no
repeated symbol in any row or column. -/
def LatinSquare (n : ℕ) : Type :=
  {L : Fin n → Fin n → Fin n // (∀ i, Injective (L i)) ∧ ∀ j, Injective fun i => L i j}

namespace LatinSquare

variable {n : ℕ}

instance : Fintype (LatinSquare n) := Subtype.fintype _

/-- Row `i` of a Latin square, as a permutation of `Fin n`. -/
noncomputable def row (L : LatinSquare n) (i : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (L.2.1 i))

/-- Column `j` of a Latin square, as a permutation of `Fin n`. -/
noncomputable def col (L : LatinSquare n) (j : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => L.1 i j) (Finite.injective_iff_bijective.mp (L.2.2 j))

/-- The sign of a Latin square: the product of the signs of all its row and column
permutations.  A Latin square is *even* if its sign is `1` and *odd* if it is `-1`. -/
noncomputable def sign (L : LatinSquare n) : ℤˣ :=
  (∏ i, Equiv.Perm.sign (L.row i)) * ∏ j, Equiv.Perm.sign (L.col j)

end LatinSquare
