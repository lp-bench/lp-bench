import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.TFAE
import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Ball


/- ---------------------------------------------------- -/
/- Paper: TOWARDS A STALLINGS-TYPE THEOREM FOR FINITE GROUPS -/
/- ---------------------------------------------------- -/

/-!
# Towards a Stallings-type theorem for finite groups

This file states the main theorem of Carmesin, Kontogeorgiou, Kurkofka and
Turner in Lean.  It deliberately reuses Mathlib's existing group- and
graph-theoretic infrastructure:

* `SimpleGraph.mulCayley`, Mathlib's Cayley graph, for the local Cayley graphs;
* `Group.IsNilpotent` and `Group.nilpotencyClass` for nilpotent groups;
* `SimpleGraph.End` for ends of graphs;
* `ZMod i` as the standard cyclic group of order `i`.

The paper-specific graph-minor notions of r-local covering and r-local
separator do not currently have a matching Mathlib API.  The graph-covering
part is made explicit below using the standard covering-graph definition:
a surjective graph homomorphism whose restriction to the closed neighborhood
of each vertex is a bijection onto the closed neighborhood of its image.
-/

open Subgroup SimpleGraph

universe u

variable (Γ : Type*) [Group Γ]

/-- The closed neighborhood of a vertex: the vertex together with its neighbors. -/
def closedNeighborSet {V : Type u} (G : SimpleGraph V) (v : V) : Set V :=
  insert v (G.neighborSet v)

/-
A graph covering map, in the standard sense: a surjective graph homomorphism
whose restriction to the closed neighborhood of each vertex `x` upstairs is a
bijection onto the closed neighborhood of `p x` downstairs.

Since a homomorphism already maps the closed neighborhood of `x` into the
closed neighborhood of `p x`, the bijectivity of the restriction is captured
by `Set.BijOn`.
-/
def IsCoveringMap {V W : Type u} (H : SimpleGraph W) (G : SimpleGraph V)
    (p : H →g G) : Prop :=
  Function.Surjective p ∧
    ∀ x : W, Set.BijOn p (closedNeighborSet H x) (closedNeighborSet G (p x))

/-
The ball predicates `IsInLocalBall` and `IsEdgeInLocalBall` are defined in
`ProofBench.PROBLEMS.P037.LocalBalls`, together with the proof that they agree
with the distance-based description of Definition 2.3 of "Local 2-separators".
-/

/- There is a walk of length at most `r` between two vertices. -/
def HasWalkLengthAtMost {V : Type u} (G : SimpleGraph V) (a b : V) (r : ℕ) : Prop :=
  ∃ w : G.Walk a b, w.length ≤ r

/-
A walk contained in `B_r(center, G)` after deleting the vertex set `deleted`.
Both its vertices and its edges are required to lie in the local ball.
-/
def WalkInLocalBallAvoiding {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (center : V) (deleted : Set V) {a b : V} (w : G.Walk a b) : Prop :=
  (∀ v : V, v ∈ w.support → IsInLocalBall G r center v ∧ v ∉ deleted) ∧
    ∀ e : Sym2 V, e ∈ w.edges → IsEdgeInLocalBall G r center e

/-- Two vertices are connected in `B_r(center, G) - deleted`. -/
def LocalBallConnectedAvoiding {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (center : V) (deleted : Set V) (a b : V) : Prop :=
  ∃ w : G.Walk a b, WalkInLocalBallAvoiding G r center deleted w

/-
The paper's `r`-local cutvertex condition: `v` is a cutvertex of the local ball
`B_r(v, G)`.
-/
def IsRLocalCutvertex {V : Type u} (G : SimpleGraph V) (r : ℕ) (v : V) : Prop :=
  ∃ a b : V,
    IsInLocalBall G r v a ∧ IsInLocalBall G r v b ∧
      a ≠ v ∧ b ≠ v ∧ ¬ LocalBallConnectedAvoiding G r v ({v} : Set V) a b

/- The external neighbourhood of the two-vertex set `{v₀, v₁}`. -/
def PairNeighbourhood {V : Type u} (G : SimpleGraph V) (v₀ v₁ a : V) : Prop :=
  a ≠ v₀ ∧ a ≠ v₁ ∧ (G.Adj v₀ a ∨ G.Adj v₁ a)

/-
Adjacency in the connectivity graph `C_r(v₀, v₁, G)` from Definition 5.1 of the
paper.  Two neighbours of `{v₀, v₁}` are adjacent when they lie in the same
component of one of the punctured balls `B_r(vᵢ) - v₀ - v₁`.
-/
def LocalConnectivityGraphAdj {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (v₀ v₁ a b : V) : Prop :=
  PairNeighbourhood G v₀ v₁ a ∧ PairNeighbourhood G v₀ v₁ b ∧
    (LocalBallConnectedAvoiding G r v₀ ({v₀, v₁} : Set V) a b ∨
      LocalBallConnectedAvoiding G r v₁ ({v₀, v₁} : Set V) a b)

/- Reachability in the connectivity graph `C_r(v₀, v₁, G)`. -/
def LocalConnectivityGraphReachable {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (v₀ v₁ a b : V) : Prop :=
  Relation.ReflTransGen (LocalConnectivityGraphAdj G r v₀ v₁) a b

/-
The paper's Definition 5.1: `{v₀, v₁}` is an `r`-local 2-separator when the
connectivity graph is disconnected and `dist(v₀,v₁) ≤ r/2`.
-/
def IsRLocalTwoSeparator {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (v₀ v₁ : V) : Prop :=
  v₀ ≠ v₁ ∧ HasWalkLengthAtMost G v₀ v₁ (r / 2) ∧
    ∃ a b : V,
      PairNeighbourhood G v₀ v₁ a ∧ PairNeighbourhood G v₀ v₁ b ∧
        ¬ LocalConnectivityGraphReachable G r v₀ v₁ a b

/- A local separator of size at most two, combining local cutvertices and local 2-separators. -/
def IsRLocalSeparatorAtMostTwo {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (X : Finset V) : Prop :=
  X.card ≤ 2 ∧
    ((∃ v : V, (X : Set V) = {v} ∧ IsRLocalCutvertex G r v) ∨
      ∃ v₀ v₁ : V,
        v₀ ≠ v₁ ∧ (X : Set V) = {v₀, v₁} ∧ IsRLocalTwoSeparator G r v₀ v₁)

/- The ordinary metric ball defined by walks of length at most `r`. -/
def MetricBall {V : Type u} (G : SimpleGraph V) (r : ℕ)
    (center : V) : Set V := { v : V | HasWalkLengthAtMost G center v r}

/-
The local-ball preservation expected of an `r`-local covering: over every
vertex, projection restricts to a bijection between the walk-metric balls of
radius `r/2`, and adjacency inside those balls is exactly reflected by
projection.
-/
def PreservesRLocalBalls {V W : Type u} (H : SimpleGraph W) (G : SimpleGraph V)
    (p : W → V) (r : ℕ) : Prop :=
  (∀ x : W, Set.BijOn p (MetricBall H (r / 2) x) (MetricBall G (r / 2) (p x))) ∧
    ∀ x y z : W,
      y ∈ MetricBall H (r / 2) x →
        z ∈ MetricBall H (r / 2) x →
          (H.Adj y z ↔ G.Adj (p y) (p z))

/- The component selected by an end outside a finite vertex set. -/
def endComponentAt {V : Type u} (G : SimpleGraph V) (K : Finset V)
    (e : G.end) : G.ComponentCompl K :=
  (e : (j : (Finset V)ᵒᵖ) → G.componentComplFunctor.obj j) (Opposite.op K)

/- Two ends are separated by `K` when they choose different components outside `K`. -/
def EndsSeparatedBy {V : Type u} (G : SimpleGraph V) (K : Finset V) : Prop :=
  ∃ e₁ e₂ : G.end,
    e₁ ≠ e₂ ∧ endComponentAt G K e₁ ≠ endComponentAt G K e₂

/- `G` has at least two ends separated by a vertex set of size at most two. -/
def HasTwoEndsSeparatedByAtMostTwo {V : Type u} (G : SimpleGraph V)
    (K : Finset V) : Prop :=
  K.card ≤ 2 ∧ EndsSeparatedBy G K


/-
Certificate for the assertion that a graph has an r-local separator of size at
most two, using the concrete local cutvertex and local 2-separator definitions
above.
-/
structure LocalSeparator {V : Type u} (G : SimpleGraph V) (r : ℕ) : Type u where
  separator : Finset V
  is_local_separator : IsRLocalSeparatorAtMostTwo G r separator

/-
Certificate for the assertion that an r-local covering of `G` has at least two
ends separated by at most two vertices.

The fields `W`, `coverGraph`, and `projection` represent the covering graph and
its projection to `G`.  The fields `is_covering_map` and
`preserves_local_balls` encode the covering-graph condition and the local
ball-preservation property used in the reference construction of r-local
coverings.  The final field states the end-separation condition using
Mathlib's `SimpleGraph.end`.
-/
structure LocalCovering {V : Type u}
    (G : SimpleGraph V) (r : ℕ) : Type (u + 1) where
  W : Type u
  coverGraph : SimpleGraph W
  projection : coverGraph →g G
  is_covering_map : IsCoveringMap coverGraph G projection
  preserves_local_balls : PreservesRLocalBalls coverGraph G ⇑projection r
  separator : Finset W
  ends_separated : HasTwoEndsSeparatedByAtMostTwo coverGraph separator

/-
Assertion (i) of Theorem 1: some Cayley graph of `Γ` has an r-local covering
with at least two ends separated by at most two vertices.
-/
def AssertionI (r : ℕ) : Prop :=
  ∃ S : Set Γ, closure S = ⊤ ∧
    Nonempty (LocalCovering ( mulCayley S) r)

/-
Assertion (ii) of Theorem 1: some Cayley graph of `Γ` has an r-local separator
of size at most two and the group has order greater than `r`.
-/
def AssertionII [Finite Γ] (r : ℕ) : Prop :=
  (∃ S : Set Γ, closure S = ⊤ ∧ Nat.card Γ > r ∧
      Nonempty (LocalSeparator ( mulCayley S) r))


/-
Assertion (iii) of Theorem 1: `Γ` is isomorphic to `C_i × C_j` for some
`i > r` and `j ∈ {1, 2}`.  We model `C_k` as the multiplicative group
`Multiplicative (ZMod k)`.
-/
def AssertionIII (r : ℕ) : Prop :=
  ∃ i j : ℕ,
    i > r ∧ j ∈ ({1, 2} : Finset ℕ) ∧
      Nonempty (Γ ≃* (Multiplicative (ZMod i) × Multiplicative (ZMod j)))

/-
Main theorem, Theorem 1 of the paper.

Let `Γ` be a finite group that is nilpotent of class at most `n`.
If `r ≥ max {4^(n+1), 20}`, then assertions (i), (ii), and (iii) are equivalent.

-/
theorem P037
    [Finite Γ] [Group.IsNilpotent Γ]
    {n r : ℕ}
    (hclass : Group.nilpotencyClass Γ ≤ n)
    (hr : max (4 ^ (n + 1)) 20 ≤ r) :
    [AssertionI Γ r, AssertionII Γ r, AssertionIII Γ r].TFAE := by sorry
