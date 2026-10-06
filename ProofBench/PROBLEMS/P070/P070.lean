import Mathlib.ModelTheory.Satisfiability

namespace P070

open FirstOrder Language

/-! ### The language of set theory -/

/-- The relation symbols of the language of set theory: a single binary
relation `∈`. -/
inductive ZFCRel : ℕ → Type
  | mem : ZFCRel 2

/-- The first-order language of set theory: no function symbols, one binary
relation symbol. -/
def zfcLang : Language :=
  ⟨fun _ => Empty, ZFCRel⟩

/-- The membership relation symbol of `zfcLang`. -/
def memRel : zfcLang.Relations 2 := ZFCRel.mem

/-- Bounded formulas of set theory with `n` free de Bruijn variables.

Convention (Mathlib's): in a fully quantified sentence read outside-in, the
first quantifier binds index `0`, the second index `1`, and so on; a
quantifier applied to a `Fm (n + 1)` binds index `n`. -/
abbrev Fm (n : ℕ) : Type := zfcLang.BoundedFormula Empty n

/-! ### Atomic formula helpers

All terms of `zfcLang` are variables, so formula combinators below take raw
de Bruijn *indices* (`ℕ`) rather than terms; the autoparams discharge the
bound checks. -/

/-- The atomic formula `xᵢ ∈ xⱼ`. -/
def memF {n : ℕ} (i j : ℕ) (hi : i < n := by omega) (hj : j < n := by omega) : Fm n :=
  memRel.boundedFormula₂ (Term.var (Sum.inr ⟨i, hi⟩)) (Term.var (Sum.inr ⟨j, hj⟩))

/-- The atomic formula `xᵢ = xⱼ`. -/
def eqF {n : ℕ} (i j : ℕ) (hi : i < n := by omega) (hj : j < n := by omega) : Fm n :=
  Term.var (Sum.inr ⟨i, hi⟩) =' Term.var (Sum.inr ⟨j, hj⟩)

/-! ### Defined notions

Each helper states a property of variables with indices below `n`; freshly
quantified variables inside a helper start at index `n`. -/

/-- `xᵢ ⊆ xⱼ` : every element of `xᵢ` is an element of `xⱼ`. -/
def subsetF {n : ℕ} (i j : ℕ) (hi : i < n := by omega) (hj : j < n := by omega) : Fm n :=
  ∀' ((memF n i) ⟹ (memF n j))

/-- `xₑ` is empty. -/
def isEmptyF {n : ℕ} (e : ℕ) (he : e < n := by omega) : Fm n :=
  ∀' ∼(memF n e)

/-- `xᵤ` is the unordered pair `{xₐ, x_b}`. -/
def isUPairF {n : ℕ} (u a b : ℕ) (hu : u < n := by omega) (ha : a < n := by omega)
    (hb : b < n := by omega) : Fm n :=
  ∀' ((memF n u) ⇔ ((eqF n a) ⊔ (eqF n b)))

/-- `x_q` is the Kuratowski ordered pair `⟨xₐ, x_b⟩ = {{xₐ}, {xₐ, x_b}}`. -/
def isOPairF {n : ℕ} (q a b : ℕ) (hq : q < n := by omega) (ha : a < n := by omega)
    (hb : b < n := by omega) : Fm n :=
  ∃' ∃' ((isUPairF n a a) ⊓ (isUPairF (n + 1) a b) ⊓ (isUPairF q n (n + 1)))

/-- The ordered pair `⟨xₐ, x_b⟩` is a member of `x_f` ("`x_f` maps `xₐ` to
`x_b`", reading `x_f` as a set of ordered pairs). -/
def pairMemF {n : ℕ} (f a b : ℕ) (hf : f < n := by omega) (ha : a < n := by omega)
    (hb : b < n := by omega) : Fm n :=
  ∃' ((memF n f) ⊓ (isOPairF n a b))

/-- `x_X ≼ x_Y` : there is an injection from `x_X` into `x_Y`, coded as a set
`f` of ordered pairs that is total on `x_X` with values in `x_Y`, functional,
and injective. -/
def injectsF {n : ℕ} (X Y : ℕ) (hX : X < n := by omega) (hY : Y < n := by omega) : Fm n :=
  ∃' ((∀' ((memF (n + 1) X) ⟹ (∃' ((memF (n + 2) Y) ⊓ (pairMemF n (n + 1) (n + 2))))))
    ⊓ (∀' ∀' ∀' (((pairMemF n (n + 1) (n + 2)) ⊓ (pairMemF n (n + 1) (n + 3))) ⟹
        (eqF (n + 2) (n + 3))))
    ⊓ (∀' ∀' ∀' (((pairMemF n (n + 1) (n + 3)) ⊓ (pairMemF n (n + 2) (n + 3))) ⟹
        (eqF (n + 1) (n + 2)))))

/-- `xₛ` is the successor `x_y ∪ {x_y}` of `x_y`. -/
def isSuccF {n : ℕ} (s y : ℕ) (hs : s < n := by omega) (hy : y < n := by omega) : Fm n :=
  ∀' ((memF n s) ⇔ ((memF n y) ⊔ (eqF n y)))

/-- `x_I` is inductive: it contains an empty set and is closed under
successor. -/
def isInductiveF {n : ℕ} (I : ℕ) (hI : I < n := by omega) : Fm n :=
  (∃' ((memF n I) ⊓ (isEmptyF n))) ⊓
    (∀' ((memF n I) ⟹ (∃' ((memF (n + 1) I) ⊓ (isSuccF (n + 1) n)))))

/-- `x_w` is `ω`: the ⊆-least inductive set. -/
def isOmegaF {n : ℕ} (w : ℕ) (hw : w < n := by omega) : Fm n :=
  (isInductiveF w) ⊓ (∀' ((isInductiveF n) ⟹ (subsetF w n)))

/-- `xₚ` is the power set of `x_w`. -/
def isPowF {n : ℕ} (p w : ℕ) (hp : p < n := by omega) (hw : w < n := by omega) : Fm n :=
  ∀' ((memF n p) ⇔ (subsetF n w))

/-! ### The ZFC axioms -/

/-- Extensionality: sets with the same elements are equal. -/
def extensionalityAx : zfcLang.Sentence :=
  ∀' ∀' ((∀' ((memF 2 0) ⇔ (memF 2 1))) ⟹ (eqF 0 1))

/-- Empty set: an empty set exists. -/
def emptySetAx : zfcLang.Sentence :=
  ∃' (isEmptyF 0)

/-- Pairing: for all `a, b` the unordered pair `{a, b}` exists. -/
def pairingAx : zfcLang.Sentence :=
  ∀' ∀' ∃' (isUPairF 2 0 1)

/-- Union: for every family `F` the union `⋃ F` exists. -/
def unionAx : zfcLang.Sentence :=
  ∀' ∃' ∀' ((memF 2 1) ⇔ (∃' ((memF 3 0) ⊓ (memF 2 3))))

/-- Power set: for every `x` the power set `P(x)` exists. -/
def powersetAx : zfcLang.Sentence :=
  ∀' ∃' (isPowF 1 0)

/-- Infinity: an inductive set exists. -/
def infinityAx : zfcLang.Sentence :=
  ∃' (isInductiveF 0)

/-- Foundation: every nonempty set has an ∈-minimal element. -/
def foundationAx : zfcLang.Sentence :=
  ∀' ((∃' (memF 1 0)) ⟹ (∃' ((memF 1 0) ⊓ (∀' ((memF 2 1) ⟹ ∼(memF 2 0))))))

/-- Choice: every family of nonempty pairwise-disjoint sets has a transversal
(a set meeting each member in exactly one point). -/
def choiceAx : zfcLang.Sentence :=
  ∀' (((∀' ((memF 1 0) ⟹ (∃' (memF 2 1)))) ⊓
        (∀' ∀' (((memF 1 0) ⊓ (memF 2 0) ⊓ ∼(eqF 1 2)) ⟹
          ∼(∃' ((memF 3 1) ⊓ (memF 3 2))))))
    ⟹ (∃' (∀' ((memF 2 0) ⟹
          (∃' ((memF 3 2) ⊓ (memF 3 1) ⊓
            (∀' (((memF 4 2) ⊓ (memF 4 1)) ⟹ (eqF 4 3)))))))))

/-- The separation (subset) axiom for a formula `φ` whose free variables are
parameters `x₀, …, x_{k-1}` and the element variable `x_k`:

`∀ params ∀ A ∃ S ∀ z (z ∈ S ↔ z ∈ A ∧ φ(params, z))`. -/
def separationAx {k : ℕ} (φ : Fm (k + 1)) : zfcLang.Sentence :=
  (∀' ∃' ∀' ((memF (k + 2) (k + 1)) ⇔ ((memF (k + 2) k) ⊓ (φ.liftAt 2 k)))).alls

/-- The replacement axiom for a formula `φ` whose free variables are
parameters `x₀, …, x_{k-1}`, the argument variable `x_k` and the value
variable `x_{k+1}`:

`∀ params ∀ A ((∀ x ∈ A, ∃! y, φ(x, y)) → ∃ B ∀ x ∈ A ∃ y ∈ B, φ(x, y))`. -/
def replacementAx {k : ℕ} (φ : Fm (k + 2)) : zfcLang.Sentence :=
  (∀' ((∀' ((memF (k + 1) k) ⟹
        (∃' (∀' (((φ.liftAt 1 k).liftAt 1 (k + 2)) ⇔ (eqF (k + 3) (k + 2)))))))
    ⟹ (∃' (∀' ((memF (k + 2) k) ⟹
        (∃' ((memF (k + 3) (k + 1)) ⊓ (φ.liftAt 2 k)))))))).alls

/-- First-order ZFC: the core axioms together with the separation and
replacement schemas (over all parameter counts). -/
def ZFC : zfcLang.Theory :=
  {extensionalityAx, emptySetAx, pairingAx, unionAx, powersetAx, infinityAx,
      foundationAx, choiceAx}
    ∪ Set.range (fun p : (k : ℕ) × Fm (k + 1) => separationAx p.2)
    ∪ Set.range (fun p : (k : ℕ) × Fm (k + 2) => replacementAx p.2)

/-! ### The Continuum Hypothesis -/

/-- The Continuum Hypothesis, in the form: every set that injects into
`P(ω)` either injects into `ω` or admits an injection from `P(ω)`.

Over ZFC (using choice for cardinal comparability and Cantor–Schröder–
Bernstein) this is equivalent to the textbook statement that no cardinality
lies strictly between `|ω|` and `|P(ω)|`, i.e. `2 ^ ℵ₀ = ℵ₁`. -/
def CH : zfcLang.Sentence :=
  ∀' ∀' (((isOmegaF 0) ⊓ (isPowF 1 0)) ⟹
    (∀' ((injectsF 2 1) ⟹ ((injectsF 2 0) ⊔ (injectsF 1 2)))))

/-! ### The challenge -/

/-- `φ` is independent of `T`: `T` neither semantically entails `φ` nor its
negation.  Mathlib's model theory has no syntactic proof calculus, so
consequence is stated semantically; by the Gödel completeness theorem this
agrees with the provability reading. -/
def Independent (T : zfcLang.Theory) (φ : zfcLang.Sentence) : Prop :=
  ¬ T ⊨ᵇ φ ∧ ¬ T ⊨ᵇ ∼φ

/-- **Option A**: the Continuum Hypothesis is a semantic consequence of the
deep-embedded first-order `ZFC`.  This problem is three-optioned: exactly one
of `P070_proof`, `P070_refutation`, `P070` is provable, and a correct
submission proves exactly one of them sorry-free (axioms at most `propext`,
`Classical.choice`, `Quot.sound`).  A kernel-checked proof of THIS option
would witness an inconsistency of Lean itself. -/
theorem P070_proof : ZFC ⊨ᵇ CH := sorry

/-- **Option B**: the negation of the Continuum Hypothesis is a semantic
consequence of `ZFC`.  As with Option A, a kernel-checked proof would
witness an inconsistency of Lean itself. -/
theorem P070_refutation : ZFC ⊨ᵇ ∼CH := sorry

set_option linter.dupNamespace false in
/-- **Option C, the futility certificate and the expected submission**: the
Continuum Hypothesis is independent of `ZFC` — the task posed by Options A
and B cannot be completed.  The certificate is unconditional (no "unless
ZFC is inconsistent" hypothesis): Lean's universes provide models of the
embedded `ZFC`, so independence is a flat theorem, witnessed by exhibiting
models of `ZFC + CH` (Gödel's constructible universe) and of `ZFC + ¬CH`
(Cohen forcing).  The Flypitch project (Han–van Doorn, CPP 2020) proved
exactly this in Lean 3. -/
theorem P070 : Independent ZFC CH := sorry

end P070
