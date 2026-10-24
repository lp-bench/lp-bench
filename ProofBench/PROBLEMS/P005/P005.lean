import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Real

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)

/-- A graph G is H-free if no induced subgraph of G is isomorphic to H. -/
def SimpleGraph.IsHFree : Prop :=
  ¬ ∃ (S : Set V), Nonempty (G.induce S ≃g H)

/-- The Erdős–Hajnal conjecture for a fixed forbidden graph H:
    there exists c > 0 such that every finite H-free graph G
    has a clique or independent set of size at least |V(G)|^c. -/
def ErdosHajnalConjectureFor [Fintype W] : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V), G.IsHFree H →
    ∃ (n : ℕ) (s : Finset V),
      (G.IsNClique n s ∨ Gᶜ.IsNClique n s) ∧
      (n : ℝ) ≥ (Fintype.card V : ℝ) ^ (c : ℝ)

/-- The Erdős–Hajnal conjecture for every path `pathGraph r` on `r` vertices. -/
def EHforPaths : Prop := ∀ r : ℕ, ErdosHajnalConjectureFor (pathGraph r)

/-- **The Erdős–Hajnal conjecture for paths** (Erdős–Hajnal 1989, case `H = P_r`): for
every `r` there is `c > 0` such that every finite `P_r`-free graph has a clique or
independent set of size at least `|V|^c`. -/
theorem P005 : EHforPaths := sorry
