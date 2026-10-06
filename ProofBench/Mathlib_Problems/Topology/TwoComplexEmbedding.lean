import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable

open scoped BigOperators

/-- An edge in the canonical encoding of a finite simplicial complex. -/
structure TwoComplexEdge where
  lo : ℕ
  hi : ℕ
deriving DecidableEq

/-- A triangle in the canonical encoding of a finite simplicial complex. -/
structure TwoComplexTriangle where
  a : ℕ
  b : ℕ
  c : ℕ
deriving DecidableEq

/-- A finite simplicial complex of dimension at most two, presented by its
numbered vertices, edges, and triangles. -/
structure FiniteTwoComplex where
  vertexCount : ℕ
  edges : List TwoComplexEdge
  triangles : List TwoComplexTriangle
deriving DecidableEq

namespace FiniteTwoComplex

/-- The presentation uses increasing vertex labels and contains the boundary
of every triangle. -/
def Valid (K : FiniteTwoComplex) : Prop :=
  K.edges.Nodup ∧ K.triangles.Nodup ∧
    (∀ e ∈ K.edges, e.lo < e.hi ∧ e.hi < K.vertexCount) ∧
    ∀ t ∈ K.triangles,
      t.a < t.b ∧ t.b < t.c ∧ t.c < K.vertexCount ∧
      { lo := t.a, hi := t.b } ∈ K.edges ∧
      { lo := t.a, hi := t.c } ∈ K.edges ∧
      { lo := t.b, hi := t.c } ∈ K.edges

/-- The coefficient of a vertex in the oriented boundary of an edge. -/
def edgeBoundaryCoeff (e : TwoComplexEdge) (v : ℕ) : ℤ :=
  (if v = e.hi then 1 else 0) - if v = e.lo then 1 else 0

/-- The coefficient of an edge in the oriented boundary of a triangle. -/
def triangleBoundaryCoeff (t : TwoComplexTriangle) (e : TwoComplexEdge) : ℤ :=
  (if e.lo = t.a ∧ e.hi = t.b then 1 else 0) -
    (if e.lo = t.a ∧ e.hi = t.c then 1 else 0) +
    if e.lo = t.b ∧ e.hi = t.c then 1 else 0

/-- The integral first simplicial homology of `K` is trivial: every integral
one-cycle is the boundary of an integral two-chain. -/
def HasTrivialFirstHomology (K : FiniteTwoComplex) : Prop :=
  ∀ z : K.edges.toFinset → ℤ,
    (∀ v : Fin K.vertexCount,
      ∑ e : K.edges.toFinset, z e * edgeBoundaryCoeff e.1 v = 0) →
    ∃ b : K.triangles.toFinset → ℤ, ∀ e : K.edges.toFinset,
      z e = ∑ t : K.triangles.toFinset, b t * triangleBoundaryCoeff t.1 e.1

/-- The standard geometric realization of a finite two-complex in barycentric
coordinates. -/
abbrev GeometricRealization (K : FiniteTwoComplex) :=
  { x : EuclideanSpace ℝ (Fin K.vertexCount) //
    (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
      ((∃ v : Fin K.vertexCount, ∀ i, x i ≠ 0 → i = v) ∨
       (∃ e ∈ K.edges, ∀ i, x i ≠ 0 → i.1 = e.lo ∨ i.1 = e.hi) ∨
       (∃ t ∈ K.triangles,
          ∀ i, x i ≠ 0 → i.1 = t.a ∨ i.1 = t.b ∨ i.1 = t.c)) }

/-- The geometric realization of `K` embeds topologically in three-space. -/
def EmbedsInR3 (K : FiniteTwoComplex) : Prop :=
  ∃ f : GeometricRealization K → EuclideanSpace ℝ (Fin 3),
    Topology.IsEmbedding f

/-- The two natural-number fields specifying each edge. -/
def edgeFields : List TwoComplexEdge → List ℕ
  | [] => []
  | e :: edges => e.lo :: e.hi :: edgeFields edges

/-- The three natural-number fields specifying each triangle. -/
def triangleFields : List TwoComplexTriangle → List ℕ
  | [] => []
  | t :: triangles => t.a :: t.b :: t.c :: triangleFields triangles

/-- The numerical serialization of a finite two-complex, including the two
list lengths needed for unambiguous parsing. -/
def fields (K : FiniteTwoComplex) : List ℕ :=
  K.vertexCount :: K.edges.length ::
    edgeFields K.edges ++ K.triangles.length :: triangleFields K.triangles

/-- Parse a prescribed number of edges from a numerical serialization. -/
def parseEdges : ℕ → List ℕ → Option (List TwoComplexEdge × List ℕ)
  | 0, rest => some ([], rest)
  | count + 1, lo :: hi :: rest => do
      let (edges, rest) ← parseEdges count rest
      some (⟨lo, hi⟩ :: edges, rest)
  | _ + 1, _ => none

/-- Parse a prescribed number of triangles from a numerical serialization. -/
def parseTriangles : ℕ → List ℕ → Option (List TwoComplexTriangle × List ℕ)
  | 0, rest => some ([], rest)
  | count + 1, a :: b :: c :: rest => do
      let (triangles, rest) ← parseTriangles count rest
      some (⟨a, b, c⟩ :: triangles, rest)
  | _ + 1, _ => none

@[simp] theorem parseEdges_edgeFields (edges : List TwoComplexEdge) (rest : List ℕ) :
    parseEdges edges.length (edgeFields edges ++ rest) = some (edges, rest) := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
      rcases e with ⟨lo, hi⟩
      simp [parseEdges, edgeFields, ih]

@[simp] theorem parseTriangles_triangleFields
    (triangles : List TwoComplexTriangle) (rest : List ℕ) :
    parseTriangles triangles.length (triangleFields triangles ++ rest) =
      some (triangles, rest) := by
  induction triangles with
  | nil => rfl
  | cons t triangles ih =>
      rcases t with ⟨a, b, c⟩
      simp [parseTriangles, triangleFields, ih]

/-- Recover a finite two-complex from a well-formed list of numerical fields. -/
def ofFields : List ℕ → Option FiniteTwoComplex
  | vertexCount :: edgeCount :: rest => do
      let (edges, rest) ← parseEdges edgeCount rest
      let triangleCount :: rest := rest | none
      let (triangles, _) ← parseTriangles triangleCount rest
      some ⟨vertexCount, edges, triangles⟩
  | _ => none

@[simp] theorem ofFields_fields (K : FiniteTwoComplex) : ofFields K.fields = some K := by
  rcases K with ⟨vertexCount, edges, triangles⟩
  simp [fields, ofFields, show parseTriangles triangles.length (triangleFields triangles) =
    some (triangles, []) by simpa using parseTriangles_triangleFields triangles []]

/-- Encode numerical fields as binary strings separated by `none`. -/
def encodeFields (numbers : List ℕ) : List (Option Bool) :=
  [none].intercalate (numbers.map fun n ↦ (Computability.encodeNat n).map some)

/-- Decode delimiter-separated binary strings into numerical fields. -/
def decodeFields (symbols : List (Option Bool)) : List ℕ :=
  (symbols.splitOn none).map fun field ↦
    Computability.decodeNat (field.filterMap id)

@[simp] theorem decodeFields_encodeFields {numbers : List ℕ} (h : numbers ≠ []) :
    decodeFields (encodeFields numbers) = numbers := by
  rw [decodeFields, encodeFields, List.splitOn_intercalate]
  · have hfilter (bits : List Bool) : (bits.map some).filterMap id = bits := by
      induction bits <;> simp_all
    rw [List.map_map]
    calc
      _ = List.map id numbers := by
        apply List.map_congr_left
        intro n _
        change Computability.decodeNat
          ((Computability.encodeNat n).map some |>.filterMap id) = id n
        rw [hfilter, Computability.decode_encodeNat]
        rfl
      _ = numbers := List.map_id numbers
  · intro field hfield
    simp only [List.mem_map] at hfield
    obtain ⟨n, -, rfl⟩ := hfield
    simp
  · simpa using h

/-- A direct delimiter-separated binary encoding of finite two-complexes. -/
def encoding : Computability.Encoding FiniteTwoComplex (Option Bool) where
  encode K := encodeFields K.fields
  decode symbols := ofFields (decodeFields symbols)
  decode_encode K := by
    rw [decodeFields_encodeFields (by simp [fields])]
    exact ofFields_fields K

/-- A deterministic decision procedure for the promised embedding problem
whose running time is eventually bounded by a constant multiple of `bound`. -/
def EmbeddabilityInTime (bound : ℕ → ℕ) : Prop :=
  ∃ answer : FiniteTwoComplex → Bool,
    (∀ K, K.Valid → K.HasTrivialFirstHomology →
      (answer K = true ↔ K.EmbedsInR3)) ∧
    ∃ machine : Turing.TM2ComputableInTime encoding.encode
        Computability.encodeBool answer,
      ∃ C N : ℕ, 0 < C ∧
        ∀ n, N ≤ n → machine.time n ≤ C * bound n

/-- Embeddability in three-space is decidable in deterministic polynomial
time on finite two-complexes with trivial integral first homology. -/
def PolynomialTimeEmbeddability : Prop :=
  ∃ d : ℕ, EmbeddabilityInTime fun n ↦ n ^ d

end FiniteTwoComplex
