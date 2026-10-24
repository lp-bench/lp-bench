import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank


open scoped BigOperators

namespace HypergraphJoints

attribute [local instance] Classical.dec

/--
An edge-colored multihypergraph on `[d]`, with `r` colors.  Edges are
indexed, so two indices may carry the same vertex set.
-/
structure ColoredMultiHypergraph (d r : ℕ) where
  edgeCount : ℕ
  edge : Fin edgeCount → Finset (Fin d)
  color : Fin edgeCount → Fin r

/--
Each color class is nonempty and simple, and color `i` consists of edges of
cardinality `d-k_i`, as in Definition 1.8.
-/
def IsUniformlyColored {d r : ℕ} (H : ColoredMultiHypergraph d r)
    (k : Fin r → ℕ) : Prop :=
  (∀ i : Fin r, ∃ e : Fin H.edgeCount, H.color e = i) ∧
    (∀ e : Fin H.edgeCount, (H.edge e).card = d - k (H.color e)) ∧
      ∀ e f : Fin H.edgeCount,
        H.color e = H.color f → H.edge e = H.edge f → e = f

/-- A nonnegative edge weight gives every vertex total incident weight at least one. -/
def WeightCovers {d r : ℕ} (H : ColoredMultiHypergraph d r)
    (w : Fin H.edgeCount → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧
    ∀ j : Fin d,
      1 ≤ (∑ e : Fin H.edgeCount, (if j ∈ H.edge e then w e else 0))

/-- The total covering weight `|w|`. -/
noncomputable def totalWeight {d r : ℕ} (H : ColoredMultiHypergraph d r)
    (w : Fin H.edgeCount → ℝ) : ℝ :=
  ∑ e : Fin H.edgeCount, w e

/-- The color subtotal `w̄_i`. -/
noncomputable def subtotal {d r : ℕ} (H : ColoredMultiHypergraph d r)
    (w : Fin H.edgeCount → ℝ) (i : Fin r) : ℝ :=
  ∑ e : Fin H.edgeCount, if H.color e = i then w e else 0

/-- Color subtotals of a covering weight are nonnegative. -/
theorem subtotal_nonneg {d r : ℕ} {H : ColoredMultiHypergraph d r}
    {w : Fin H.edgeCount → ℝ} (hw : WeightCovers H w) (i : Fin r) :
    0 ≤ subtotal H w i := by
  unfold subtotal
  exact Finset.sum_nonneg fun e _ => by
    split_ifs
    · exact hw.1 e
    · exact le_rfl

/-- The ambient `d`-dimensional vector space over `𝔽`. -/
abbrev Ambient (𝔽 : Type*) (d : ℕ) := Fin d → 𝔽

/-- An affine flat, represented by one base point and its direction subspace. -/
structure AffineFlat (𝔽 : Type*) [Field 𝔽] (d : ℕ) where
  base : Ambient 𝔽 d
  direction : Submodule 𝔽 (Ambient 𝔽 d)

namespace AffineFlat

/-- Membership in the affine translate `base + direction`. -/
def Contains {𝔽 : Type*} [Field 𝔽] {d : ℕ}
    (F : AffineFlat 𝔽 d) (p : Ambient 𝔽 d) : Prop :=
  p - F.base ∈ F.direction

end AffineFlat

/-- The coordinate subspace spanned by basis directions outside the edge `e`. -/
def coordinateComplementSubspace (𝔽 : Type*) [Field 𝔽] {d : ℕ}
    (e : Finset (Fin d)) : Submodule 𝔽 (Ambient 𝔽 d) where
  carrier := {v | ∀ j ∈ e, v j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j hj
    simp [hx j hj, hy j hj]
  smul_mem' := by
    intro a x hx j hj
    simp [hx j hj]

/-- Indexed flat multisets, one finite family for every color. -/
structure ColoredFlatFamily (d r : ℕ) (𝔽 : Type*) [Field 𝔽]
    (k : Fin r → ℕ) where
  flatCount : Fin r → ℕ
  flat : ∀ i : Fin r, Fin (flatCount i) → AffineFlat 𝔽 d
  dimension : ∀ i a, Module.finrank 𝔽 (flat i a).direction = k i

/-- A choice of one flat occurrence for every edge of `H`. -/
abbrev FlatSelection {d r : ℕ} (H : ColoredMultiHypergraph d r)
    {𝔽 : Type*} [Field 𝔽] {k : Fin r → ℕ}
    (family : ColoredFlatFamily d r 𝔽 k) :=
  (e : Fin H.edgeCount) → Fin (family.flatCount (H.color e))

/--
The selected flats form an `H`-joint at `p` (Definition 1.8): with `A = p + L`,
each selected flat is the image under `A` of the coordinate subspace spanned by
the basis vectors outside its edge.
-/
def FormsHJointAt {d r : ℕ} (H : ColoredMultiHypergraph d r)
    {𝔽 : Type*} [Field 𝔽] {k : Fin r → ℕ}
    (family : ColoredFlatFamily d r 𝔽 k) (p : Ambient 𝔽 d)
    (selection : FlatSelection H family) : Prop :=
  ∃ L : Ambient 𝔽 d ≃ₗ[𝔽] Ambient 𝔽 d,
    ∀ e : Fin H.edgeCount,
      let F := family.flat (H.color e) (selection e)
      F.Contains p ∧
        F.direction =
          (coordinateComplementSubspace 𝔽 (H.edge e)).map L.toLinearMap

/-- An `H`-joints configuration: flat families and the finite set of all their `H`-joints. -/
structure HJointConfiguration (d r : ℕ) (H : ColoredMultiHypergraph d r)
    (𝔽 : Type*) [Field 𝔽] (k : Fin r → ℕ) where
  family : ColoredFlatFamily d r 𝔽 k
  joints : Finset (Ambient 𝔽 d)
  mem_joints_iff : ∀ p,
    p ∈ joints ↔
      ∃ selection : FlatSelection H family,
        FormsHJointAt H family p selection

namespace HJointConfiguration

/-- A point is listed exactly when it is an `H`-joint. -/
@[simp] theorem mem_joints {d r : ℕ} {H : ColoredMultiHypergraph d r}
    {𝔽 : Type*} [Field 𝔽] {k : Fin r → ℕ}
    (C : HJointConfiguration d r H 𝔽 k) (p : Ambient 𝔽 d) :
    p ∈ C.joints ↔
      ∃ selection : FlatSelection H C.family,
        FormsHJointAt H C.family p selection :=
  C.mem_joints_iff p

end HJointConfiguration

/-- The constant `C_(H,w)` from Theorem 1.12. -/
noncomputable def jointConstant {d r : ℕ}
    (H : ColoredMultiHypergraph d r) (k : Fin r → ℕ)
    (w : Fin H.edgeCount → ℝ) : ℝ :=
  Real.rpow (Nat.factorial d : ℝ) (totalWeight H w - 1) *
    (∏ i : Fin r,
      Real.rpow (1 / (Nat.factorial (k i) : ℝ)) (subtotal H w i)) *
      ∏ e : Fin H.edgeCount,
        Real.rpow (w e / subtotal H w (H.color e)) (w e)

/-- The product `|F₁|^w̄₁ ... |Fᵣ|^w̄ᵣ` in the theorem. -/
noncomputable def flatFamilyProduct {d r : ℕ}
    {H : ColoredMultiHypergraph d r} {𝔽 : Type*} [Field 𝔽]
    {k : Fin r → ℕ} (C : HJointConfiguration d r H 𝔽 k)
    (w : Fin H.edgeCount → ℝ) : ℝ :=
  ∏ i : Fin r,
    Real.rpow (C.family.flatCount i : ℝ) (subtotal H w i)

/--
For every covering weight `w`, an `H`-joints configuration has at most
`C_(H,w) · |F₁|^w̄₁ ⋯ |Fᵣ|^w̄ᵣ` joints.
Theorem 1.12 (simple `H`-joints) of Chao–Yu, arXiv:2410.06498.
-/
theorem P053
    {d r : ℕ} (H : ColoredMultiHypergraph d r)
    (k : Fin r → ℕ)
    (hk : ∀ i, 1 ≤ k i ∧ k i ≤ d - 1)
    (hUniform : IsUniformlyColored H k)
    (w : Fin H.edgeCount → ℝ) (hw : WeightCovers H w)
    (𝔽 : Type*) [Field 𝔽]
    (C : HJointConfiguration d r H 𝔽 k) :
    (C.joints.card : ℝ) ≤ jointConstant H k w * flatFamilyProduct C w := by
  sorry

end HypergraphJoints
