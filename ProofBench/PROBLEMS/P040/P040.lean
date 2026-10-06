import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/- ==============================================================================
P040 — A recolouring version of a conjecture of Reed
(L. De Meyer et al., arXiv:2502.10147, Theorem 4).

Reed's conjecture bounds the chromatic number by `⌈(ω(G) + Δ(G) + 1)/2⌉`.  This
problem is the recolouring analogue for odd-hole-free-like graphs: with
`f(G) = max_v ⌈(ω(v) + deg(v) + 1)/2⌉`,

  (i)  if every odd hole of `G` contains a vertex of degree at most `f(G)`,
       then all `k`-colourings of `G` are Kempe equivalent for every `k > f(G)`;
  (ii) for every `k ≥ 3` there is a perfect graph with a non-unique frozen
       `k`-colouring — hence not `k`-recolourable — where `k` is exactly one
       below the global Reed half-bound `⌈(ω(G) + Δ(G) + 1)/2⌉`.

The two parts are packaged as the single target `P040`.
============================================================================== -/

open SimpleGraph

namespace RecolouringReed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Local Reed parameters -/

/-- The closed neighbourhood `N[v]`, as a finite set. -/
noncomputable def closedNeighbourFinset (G : SimpleGraph V) (v : V) : Finset V :=
  insert v (G.neighborSet v).toFinite.toFinset

/-- The finite local clique number `ω(v)`: the largest clique containing `v`. -/
noncomputable def localCliqueNumber (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset V)).filter
    (fun s : Finset V ↦ v ∈ s ∧ G.IsClique (s : Set V))).sup Finset.card

/-- The degree of a vertex, with the finite-neighbourhood instance supplied explicitly.
Mathlib's `SimpleGraph.degree` is indexed by `Fintype ↑(G.neighborSet v)`; this helper
avoids instance-search failures in definitions that only assume `[Fintype V]`. -/
noncomputable def vertexDegree (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  letI : Fintype ↑(G.neighborSet v) := (G.neighborSet v).toFinite.fintype
  exact G.degree v

/-- The maximum degree `Δ(G)`. -/
noncomputable def maxDegree (G : SimpleGraph V) : ℕ :=
  (Finset.univ : Finset V).sup (vertexDegree G)

/-- The local Reed bound `⌈(ω(v) + deg(v) + 1)/2⌉`. -/
noncomputable def localReedBound (G : SimpleGraph V) (v : V) : ℕ :=
  (localCliqueNumber G v + vertexDegree G v + 2) / 2

/-- The paper's local parameter `f(G) = max_v ⌈(ω(v) + deg(v) + 1)/2⌉`. -/
noncomputable def reedLocalParameter (G : SimpleGraph V) : ℕ :=
  (Finset.univ : Finset V).sup (localReedBound G)

/-- The global Reed half-bound `⌈(ω(G) + Δ(G) + 1)/2⌉`. -/
noncomputable def globalReedHalfBound (G : SimpleGraph V) : ℕ :=
  (G.cliqueNum + maxDegree G + 2) / 2

/-! ## Kempe changes and recolourability -/

/-- A set of vertices using only two colours under a colouring. -/
def UsesOnlyTwoColors {W : Type*} {G : SimpleGraph W} {k : ℕ} (C : G.Coloring (Fin k))
    (a b : Fin k) (S : Set W) : Prop :=
  ∀ v, v ∈ S → C v = a ∨ C v = b

/-- A Kempe chain is a maximal connected bichromatic component; the empty chain is
allowed (it accounts for colour pairs that do not occur). -/
structure KempeChain {W : Type*} (G : SimpleGraph W) {k : ℕ} (C : G.Coloring (Fin k)) where
  leftColor : Fin k
  rightColor : Fin k
  support : Set W
  colors : UsesOnlyTwoColors C leftColor rightColor support
  connected_or_empty : support = ∅ ∨ (G.induce support).Connected
  maximal :
    ∀ T : Set W,
      support ⊆ T →
      UsesOnlyTwoColors C leftColor rightColor T →
      (T = ∅ ∨ (G.induce T).Connected) →
      T = support

/-- Swapping two distinguished colours. -/
def swapColors {k : ℕ} (a b : Fin k) (c : Fin k) : Fin k :=
  if c = a then b else if c = b then a else c

theorem swapColors_left {k : ℕ} (a b : Fin k) : swapColors a b a = b := by
  simp [swapColors]

theorem swapColors_right {k : ℕ} {a b : Fin k} (h : a ≠ b) : swapColors a b b = a := by
  simp [swapColors, h.symm]

theorem swapColors_of_ne {k : ℕ} {a b c : Fin k} (ha : c ≠ a) (hb : c ≠ b) :
    swapColors a b c = c := by
  simp [swapColors, ha, hb]

/-- `IsKempeChange G C D K` says that `D` is obtained from `C` by swapping the two colours
of the chain `K` exactly on `K.support`.  Phrased as a conjunction of guarded equalities
to avoid needing `Decidable (v ∈ K.support)` for an `if`-`then`-`else`. -/
def IsKempeChange {W : Type*} {k : ℕ} (G : SimpleGraph W) (C D : G.Coloring (Fin k))
    (K : KempeChain G C) : Prop :=
  ∀ v,
    (v ∈ K.support → D v = swapColors K.leftColor K.rightColor (C v)) ∧
    (v ∉ K.support → D v = C v)

/-- Kempe equivalence is reachability under finitely many Kempe changes. -/
def KempeEquivalent {W : Type*} {k : ℕ} (G : SimpleGraph W) :
    G.Coloring (Fin k) → G.Coloring (Fin k) → Prop :=
  Relation.ReflTransGen (fun C D ↦ ∃ K : KempeChain G C, IsKempeChange G C D K)

theorem kempeEquivalent_refl {W : Type*} {k : ℕ} (G : SimpleGraph W)
    (C : G.Coloring (Fin k)) : KempeEquivalent G C C :=
  Relation.ReflTransGen.refl

theorem kempeEquivalent_trans {W : Type*} {k : ℕ} (G : SimpleGraph W)
    {A B C : G.Coloring (Fin k)}
    (hAB : KempeEquivalent G A B) (hBC : KempeEquivalent G B C) :
    KempeEquivalent G A C :=
  hAB.trans hBC

/-- A graph is `k`-recolourable when all its `k`-colourings are Kempe equivalent. -/
def KRecolourable {W : Type*} (G : SimpleGraph W) (k : ℕ) : Prop :=
  ∀ C D : G.Coloring (Fin k), KempeEquivalent G C D

/-! ## Frozen colourings and perfect graphs -/

/-- A frozen colouring: every pair of distinct colours induces a connected subgraph.
This is the paper's standard obstruction to Kempe recolourability. -/
def FrozenColoring {W : Type*} {k : ℕ} (G : SimpleGraph W) (C : G.Coloring (Fin k)) :
    Prop :=
  ∀ a b : Fin k, a ≠ b → (G.induce {v | C v = a ∨ C v = b}).Connected

/-- A colouring is unique up to permuting colours. -/
def UniqueUpToPermutingColors {W : Type*} {k : ℕ} (G : SimpleGraph W)
    (C : G.Coloring (Fin k)) : Prop :=
  ∀ D : G.Coloring (Fin k), ∃ e : Fin k ≃ Fin k, ∀ v, D v = e (C v)

/-- The existence of a non-unique frozen colouring. -/
def HasNonuniqueFrozenColoring {W : Type*} (G : SimpleGraph W) (k : ℕ) : Prop :=
  ∃ C : G.Coloring (Fin k), FrozenColoring G C ∧ ¬ UniqueUpToPermutingColors G C

/-- Perfectness, stated using Mathlib's chromatic number and clique number. -/
def PerfectGraph {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ S : Set W, (G.induce S).chromaticNumber = (G.induce S).cliqueNum

/-! ## Odd holes -/

/-- An induced `n`-cycle of `G`, presented by a cyclic indexing `c : ZMod n → V`.

The map `c` is injective, and two vertices are adjacent **exactly** when their indices
are cyclically consecutive (`i - j = 1` or `j - i = 1`).  The forward direction of the
biconditional forces the cycle edges to be present; the backward direction forbids
chords, so the induced subgraph on `Set.range c` is precisely the cycle `C n`. -/
def IsInducedCycleOn {W : Type*} (G : SimpleGraph W) (n : ℕ) (c : ZMod n → W) : Prop :=
  Function.Injective c ∧
    ∀ i j : ZMod n, G.Adj (c i) (c j) ↔ (i - j = 1 ∨ j - i = 1)

/-- `S` is an **odd hole** of `G`: the vertex set of an induced cycle of odd length at
least `5`.  A hole is an induced cycle of length at least `4`; oddness then forces
length at least `5`, which is recorded explicitly by `5 ≤ n`. -/
def IsOddHole {W : Type*} (G : SimpleGraph W) (S : Set W) : Prop :=
  ∃ (n : ℕ) (c : ZMod n → W),
    5 ≤ n ∧ Odd n ∧ IsInducedCycleOn G n c ∧ S = Set.range c

/-- The hypothesis of Theorem 4.(i): every odd hole of `G` contains a vertex whose
degree **in `G`** is at most `f(G) = reedLocalParameter G`. -/
def EveryOddHoleHasSmallVertex (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, IsOddHole G S → ∃ v ∈ S, vertexDegree G v ≤ reedLocalParameter G

/-! ## The two parts of Theorem 4 -/

/-- **Theorem 4.(i)** of arXiv:2502.10147: if every odd hole of `G` contains a vertex
of degree at most `f(G)`, then `G` is `k`-recolourable for every `k > f(G)`. -/
def ReedRecolouringOddHoles : Prop :=
  ∀ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    EveryOddHoleHasSmallVertex G →
      ∀ k : ℕ, reedLocalParameter G < k → KRecolourable G k

/-- **Theorem 4.(ii)** of arXiv:2502.10147: for every `k ≥ 3` there is a perfect graph
with a non-unique frozen `k`-colouring — hence not `k`-recolourable — exactly one
colour below the global Reed half-bound. -/
def FrozenPerfectGraphs : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W),
      PerfectGraph G ∧
      HasNonuniqueFrozenColoring G k ∧
      ¬ KRecolourable G k ∧
      k = globalReedHalfBound G - 1

/-- **A recolouring version of a conjecture of Reed** (Theorem 4 of
arXiv:2502.10147): the odd-hole recolouring bound together with its tightness on
perfect graphs. -/
theorem P040 : ReedRecolouringOddHoles ∧ FrozenPerfectGraphs := by
  sorry

end RecolouringReed
