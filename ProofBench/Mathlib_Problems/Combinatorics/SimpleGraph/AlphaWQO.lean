import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.WagnerPlanarity
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# α-well-quasi-ordering (Nash–Williams hierarchy) and the minor order
-/

open SimpleGraph

noncomputable section

universe u

variable {Q Q' : Type u}

/- A quasi-order is well-quasi-ordered when every infinite sequence
contains an increasing pair. -/
def IsWQO (le : Q → Q → Prop) : Prop :=
  ∀ f : ℕ → Q, ∃ i j : ℕ, i < j ∧ le (f i) (f j)

/- Level `o` of the cumulative hierarchy over `Q`: `VStar Q 0 = Q`,
`VStar Q (succ o)` is the nonempty subsets of `VStar Q o`, and at a limit
`o` it is the disjoint union of all lower levels, reindexed through
`o.ToType` to stay in `Type u`. -/
variable (Q) in
def VStar (o : Ordinal.{u}) : Type u :=
  Ordinal.limitRecOn o
    Q
    (fun _ ih => {S : Set ih // S.Nonempty})
    (fun o _ ih => Σ i : o.ToType, ih (Ordinal.typein (α := o.ToType) (· < ·) i)
      (Ordinal.typein_lt_self i))

variable (Q) in
theorem VStar_zero : VStar Q 0 = Q :=
  Ordinal.limitRecOn_zero ..

variable (Q) in
theorem VStar_succ (o : Ordinal.{u}) :
    VStar Q (Order.succ o) = {S : Set (VStar Q o) // S.Nonempty} :=
  Ordinal.limitRecOn_add_one ..

variable (Q) in
theorem VStar_limit {o : Ordinal.{u}} (h : Order.IsSuccLimit o) :
    VStar Q o = Σ i : o.ToType, VStar Q (Ordinal.typein (α := o.ToType) (· < ·) i) :=
  Ordinal.limitRecOn_limit _ _ _ _ h

/- The Nash–Williams game relation `≤*`, as a *heterogeneous* relation
comparing an element of level `a` with an element of level `b`.
-/
def leStar (le : Q → Q → Prop) (a : Ordinal.{u}) :
    VStar Q a → ∀ b : Ordinal.{u}, VStar Q b → Prop :=
  Ordinal.limitRecOn (motive := fun a => VStar Q a → ∀ b : Ordinal.{u}, VStar Q b → Prop) a
    -- a = 0 : X is in Q, Player I cannot move; recurse on b (Player II descends).
    (fun X b => Ordinal.limitRecOn (motive := fun b => VStar Q b → Prop) b
      (fun Y => le (cast (VStar_zero Q) X) (cast (VStar_zero Q) Y))
      (fun β ibh Y => ∃ y ∈ (cast (VStar_succ Q β) Y).val, ibh y)
      (fun β hb ibh Y =>
        let Y' := cast (VStar_limit Q hb) Y
        ibh (Ordinal.typein (α := β.ToType) (· < ·) Y'.1) (Ordinal.typein_lt_self _) Y'.2))
    -- a = succ α : Player I picks x ∈ X, then Player II answers from b.
    (fun α ih X b => Ordinal.limitRecOn (motive := fun b => VStar Q b → Prop) b
      (fun Y => ∀ x ∈ (cast (VStar_succ Q α) X).val, ih x 0 Y)
      (fun β _ Y => ∀ x ∈ (cast (VStar_succ Q α) X).val,
        ∃ y ∈ (cast (VStar_succ Q β) Y).val, ih x β y)
      (fun β hb ibh Y =>
        let Y' := cast (VStar_limit Q hb) Y
        ibh (Ordinal.typein (α := β.ToType) (· < ·) Y'.1) (Ordinal.typein_lt_self _) Y'.2))
    -- a limit : X is a disjoint-union tag; unwrap to its underlying element.
    (fun a ha iha X =>
      let X' := cast (VStar_limit Q ha) X
      iha (Ordinal.typein (α := a.ToType) (· < ·) X'.1) (Ordinal.typein_lt_self _) X'.2)

/- `(Q, le)` is `α`-well-quasi-ordered when level `α` of
 the cumulative hierarchy over `Q` is well-quasi-ordered under `≤*`. -/
def IsAlphaWQO (le : Q → Q → Prop) (a : Ordinal.{u}) : Prop :=
  IsWQO (fun X Y : VStar Q a => leStar le a X a Y)

structure FiniteGraph where
  V : Type
  [fintypeV : Fintype V]
  graph : SimpleGraph V

attribute [instance] FiniteGraph.fintypeV

def FiniteGraph.MinorLE (G H : FiniteGraph) : Prop :=
  Nonempty (Minor G.graph H.graph)

/- A finite planar simple graph. -/
def PlanarGraph : Type 1 :=
  {G : FiniteGraph // G.graph.IsWagnerPlanar}

/- The minor order on finite planar graphs. -/
def PlanarGraph.MinorLE (G H : PlanarGraph) : Prop :=
  FiniteGraph.MinorLE G.val H.val

/-! ### Unfolding the `limitRecOn` recursions

`VStar` and `leStar` recurse through `Ordinal.limitRecOn`. -/

/-! ### The hierarchy functor and transfer of `α`-WQO along order-reflecting maps -/
/- A map `g : Q → Q'` induces a map between the cumulative hierarchies, level by
level: at level `0` it is `g` itself, at successor levels it takes (nonempty)
images, and at limit levels it acts on the underlying lower-level element. -/
def VStar.map (g : Q → Q') (a : Ordinal.{u}) : VStar Q a → VStar Q' a :=
  Ordinal.limitRecOn (motive := fun a => VStar Q a → VStar Q' a) a
    (fun X => cast (VStar_zero Q').symm (g (cast (VStar_zero Q) X)))
    (fun α ih X =>
      cast (VStar_succ Q' α).symm
        ⟨ih '' (cast (VStar_succ Q α) X).val, (cast (VStar_succ Q α) X).property.image ih⟩)
    (fun a ha iha X =>
      cast (VStar_limit Q' ha).symm
        ⟨(cast (VStar_limit Q ha) X).1,
          iha (Ordinal.typein (α := a.ToType) (· < ·) (cast (VStar_limit Q ha) X).1)
            (Ordinal.typein_lt_self _) (cast (VStar_limit Q ha) X).2⟩)

/-! ### Level monotonicity -/