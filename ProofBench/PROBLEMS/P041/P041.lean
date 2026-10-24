import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-- A Boolean literal over `n` variables.  `positive = false` represents a
negated literal. -/
structure Literal (n : ℕ) where
  var : Fin n
  positive : Bool
deriving DecidableEq

namespace Literal

/-- Evaluation of a literal under a truth assignment. -/
def eval {n : ℕ} (τ : Fin n → Bool) (l : Literal n) : Bool :=
  if l.positive then τ l.var else !(τ l.var)

end Literal

/-- A 3-CNF formula, represented as a finite list of ordered triples of
literals. -/
structure ThreeCNF where
  numVars : ℕ
  clauses : List (Literal numVars × Literal numVars × Literal numVars)

namespace ThreeCNF

/-- A single clause is satisfied if at least one of its three literals
evaluates to true. -/
def ClauseSatisfied {n : ℕ} (τ : Fin n → Bool)
    (C : Literal n × Literal n × Literal n) : Prop :=
  C.1.eval τ = true ∨ C.2.1.eval τ = true ∨ C.2.2.eval τ = true

/-- A 3-CNF formula is satisfiable if some Boolean assignment satisfies all
clauses. -/
def Satisfiable (F : ThreeCNF) : Prop :=
  ∃ τ : Fin F.numVars → Bool, ∀ C ∈ F.clauses, ClauseSatisfied τ C

end ThreeCNF

/-- A house index on an equator of size `m`. -/
abbrev HouseIndex (m : ℕ) := Fin m

/-- An allocation assigns a Boolean truth value to each indexed house. -/
abbrev Allocation (m : ℕ) := HouseIndex m → Bool

/-- Equality constraints on allocations. -/
def EQ {m : ℕ} (P : Finset (HouseIndex m × HouseIndex m)) : Set (Allocation m) :=
  {f | ∀ p ∈ P, f p.1 = f p.2}

/-- Inequality constraints on allocations. -/
def NEQ {m : ℕ} (P : Finset (HouseIndex m × HouseIndex m)) : Set (Allocation m) :=
  {f | ∀ p ∈ P, f p.1 ≠ f p.2}

/-- OR constraints on ordered triples of houses. -/
def ORConstraints {m : ℕ}
    (K : Finset (HouseIndex m × HouseIndex m × HouseIndex m)) : Set (Allocation m) :=
  {f | ∀ t ∈ K, f t.1 = true ∨ f t.2.1 = true ∨ f t.2.2 = true}

namespace Literal

/-- The house carrying a literal: `2·var` for the positive literal `x_var`,
`2·var + 1` for the negated literal `¬x_var`. -/
def house {n : ℕ} (l : Literal n) : HouseIndex (2 * n) :=
  ⟨2 * l.var.val + (if l.positive then 0 else 1), by
    have := l.var.isLt
    split <;> omega⟩

end Literal

/-- The complementary pairs `(2i, 2i+1)`: the houses of `xᵢ` and `¬xᵢ`. -/
def complementaryPairs (n : ℕ) :
    Finset (HouseIndex (2 * n) × HouseIndex (2 * n)) :=
  Finset.univ.image fun i : Fin n =>
    ((Literal.mk i true).house, (Literal.mk i false).house)

/-- The OR triples of a formula: the houses of the three literals of each
clause. -/
def clauseTriples (F : ThreeCNF) :
    Finset (HouseIndex (2 * F.numVars) × HouseIndex (2 * F.numVars) ×
      HouseIndex (2 * F.numVars)) :=
  F.clauses.toFinset.image fun C => (C.1.house, C.2.1.house, C.2.2.house)

/-- A 3-CNF formula is satisfiable if and only if some Boolean allocation of its `2·numVars`
houses satisfies the NEQ constraints on the complementary pairs and the OR constraints of its
clauses: the combinatorial step of Lemma 3.2 of Carmesin–Turner, arXiv:2512.06403. -/
theorem P041 (F : ThreeCNF) :
    F.Satisfiable ↔
      ∃ f : Allocation (2 * F.numVars),
        f ∈ NEQ (complementaryPairs F.numVars) ∩
          ORConstraints (clauseTriples F) := by
  sorry
