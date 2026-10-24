import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.SetTheory.Cardinal.Finite

open Function Equiv

universe u

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The set of darts of `G` based at the vertex `v`. -/
def dartsAt (v : V) : Set G.Dart := {d | d.fst = v}

/-- Membership in `dartsAt`. -/
@[simp]
lemma mem_dartsAt {v : V} {d : G.Dart} : d ∈ G.dartsAt v ↔ d.fst = v := Iff.rfl

/-- The involution reversing every dart, as a permutation. -/
def dartRev : Perm G.Dart := Dart.symm_involutive.toPerm _

/-- `dartRev` reverses a dart. -/
@[simp]
lemma dartRev_apply (d : G.Dart) : G.dartRev d = d.symm := rfl

/-- A *rotation system* on `G`: a permutation of the darts that acts as a single cycle on the
darts based at each vertex, recording the cyclic order of the edge-ends around it. By the
Heffter–Edmonds principle, this is a cellular embedding of `G` into closed oriented surfaces,
one per connected component. -/
structure RotationSystem where
  /-- The underlying permutation of darts: each dart is sent to the next dart
  based at the same vertex, in the cyclic order around that vertex. -/
  rot : Perm G.Dart
  /-- At each vertex, the rotation restricts to a single cycle on the darts
  based there. -/
  isCycleOn_dartsAt : ∀ v : V, rot.IsCycleOn (G.dartsAt v)

namespace RotationSystem

variable {G} (R : G.RotationSystem)

/-- A rotation system is determined by its permutation. -/
@[ext]
lemma ext {R₁ R₂ : G.RotationSystem} (h : R₁.rot = R₂.rot) : R₁ = R₂ := by
  cases R₁; cases R₂; simpa using h

/-- The rotation keeps the base vertex of a dart. -/
@[simp]
lemma fst_rot (d : G.Dart) : (R.rot d).fst = d.fst :=
  (R.isCycleOn_dartsAt d.fst).1.mapsTo rfl

/-- The mirror image of a rotation system: reverse the cyclic order of the
darts around every vertex. -/
def reflect : G.RotationSystem where
  rot := R.rot⁻¹
  isCycleOn_dartsAt v := (R.isCycleOn_dartsAt v).inv

/-- The permutation of the mirror image is the inverse permutation. -/
@[simp]
lemma reflect_rot : R.reflect.rot = R.rot⁻¹ := rfl

/-- Reflecting twice gives back the rotation system. -/
@[simp]
lemma reflect_reflect : R.reflect.reflect = R :=
  ext (by simp)

/-- The face permutation of a rotation system: reverse the dart, then rotate.
Its orbits traverse the boundaries of the faces of the associated
embedding. -/
def faceMap : Perm G.Dart := R.rot * G.dartRev

/-- The face permutation sends `d` to the rotation of its reverse. -/
lemma faceMap_apply (d : G.Dart) : R.faceMap d = R.rot d.symm := rfl

/-- Two darts lie on the same face iff they are in the same orbit of the face
permutation. -/
def faceSetoid : Setoid G.Dart :=
  ⟨R.faceMap.SameCycle,
    ⟨Perm.SameCycle.refl _, fun h => h.symm, fun h h' => h.trans h'⟩⟩

/-- The faces of a rotation system that are traced out by darts: the orbits
of the face permutation.  Isolated vertices contribute faces separately; see
`numFaces`. -/
abbrev DartFaces : Type u := Quotient R.faceSetoid

/-- The number of faces of the embedding described by a rotation system: the orbits of the face
permutation, plus one face for each isolated vertex (meaningful for finite graphs only). -/
noncomputable def numFaces : ℕ :=
  Nat.card R.DartFaces + Nat.card ↥(G.supportᶜ)

/-- The Euler characteristic `#vertices − #edges + #faces` of a rotation system. For a finite
graph it equals `Σ (2 − 2·genus c)` over the connected components `c` of `G`, so it is at most
`2 * Nat.card G.ConnectedComponent`, with equality iff each component is embedded in a sphere. -/
noncomputable def eulerChar : ℤ :=
  (Nat.card V : ℤ) - (Nat.card G.edgeSet : ℤ) + (R.numFaces : ℤ)

/-- A rotation system is *planar* when it attains the Euler bound `2` per
connected component, i.e. embeds every component of `G` in a sphere. -/
def IsPlanar [Finite V] : Prop :=
  R.eulerChar = 2 * Nat.card G.ConnectedComponent

end RotationSystem

/-- A finite simple graph has *genus zero* if some rotation system embeds every connected
component in a sphere. By the Heffter–Edmonds principle, this is equivalent to planarity. -/
def IsGenusZero [Finite V] : Prop :=
  ∃ R : G.RotationSystem, R.IsPlanar

end SimpleGraph
