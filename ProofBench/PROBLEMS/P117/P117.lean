/-- A finite simple graph on the vertices `Fin n`, given by a Boolean adjacency relation
that is symmetric and has no loops. -/
structure FinGraph (n : Nat) where
  /-- `adj u v = true` iff `u` and `v` are adjacent. -/
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ v, adj v v = false

namespace FinGraph

variable {n : Nat}

/-- The number of neighbours of `v`. -/
def degree (G : FinGraph n) (v : Fin n) : Nat :=
  ((List.finRange n).filter (G.adj v)).length

/-- The maximum degree of `G` (`0` if `G` has no vertices). -/
def maxDegree (G : FinGraph n) : Nat :=
  ((List.finRange n).map G.degree).foldr max 0

/-- `c` is a proper edge colouring of `G` with `k` colours, given on ordered pairs: both
orientations of an edge get the same colour, and two distinct edges at a common vertex get
different colours. -/
def IsProperEdgeColouring {k : Nat} (G : FinGraph n) (c : Fin n → Fin n → Fin k) : Prop :=
  (∀ u v, G.adj u v = true → c u v = c v u) ∧
    ∀ u v w, G.adj u v = true → G.adj u w = true → v ≠ w → c u v ≠ c u w

/-- `G` has a proper edge colouring with `k` colours. -/
def EdgeColourable (G : FinGraph n) (k : Nat) : Prop :=
  ∃ c : Fin n → Fin n → Fin k, G.IsProperEdgeColouring c

end FinGraph

/-- **Vizing's theorem, constructively** (Vizing 1964; algorithmic proof by Misra and Gries
1992): every finite simple graph has a proper edge colouring with `Δ + 1` colours.

Constructive track: the proof may use the axioms `propext` and `Quot.sound` but not
`Classical.choice` (`#print axioms P117`). -/
theorem P117 {n : Nat} (G : FinGraph n) : G.EdgeColourable (G.maxDegree + 1) := sorry
