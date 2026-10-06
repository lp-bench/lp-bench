import ProofBench.Mathlib_Problems.Combinatorics.Multigraph.CycleDoubleCover

namespace Multigraph

variable {V E : Type*} (M : Multigraph V E)

/-- The first endpoint of an edge in a fixed representative orientation. -/
noncomputable def firstEnd (e : E) : V := (M.ends e).out.1

/-- The second endpoint of an edge in a fixed representative orientation. -/
noncomputable def secondEnd (e : E) : V := (M.ends e).out.2

/-- A nowhere-zero `A`-flow with respect to the representative orientation:
every value is nonzero and Kirchhoff's law holds at every vertex, `f e`
leaving `firstEnd e` and entering `secondEnd e`.  Reorienting an edge
corresponds to negating its value, so the orientation choice is immaterial;
a loop enters both sums and cancels, so loops are unconstrained. -/
def IsNowhereZeroFlow [Fintype E] [DecidableEq V] {A : Type*} [AddCommGroup A]
    (f : E → A) : Prop :=
  (∀ e, f e ≠ 0) ∧
    ∀ v : V, ∑ e ∈ Finset.univ.filter (fun e => M.firstEnd e = v), f e
      = ∑ e ∈ Finset.univ.filter (fun e => M.secondEnd e = v), f e

end Multigraph
