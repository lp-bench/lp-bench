module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Maps
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace SimpleGraph
variable {V W : Type*} {G : SimpleGraph V} {s t : Set V} {u u' v w : V}

-- TODO: Replace in mathlib
/-! ### Reachability on a set -/

variable (G s) in
/-- Two vertices `u` and `v` are reachable in a graph `G` on `s` if there exists a walk from `u` to
`v` in `G` whose vertices all lie within `s`. -/
def ReachableOn (u v : V) : Prop := ∃ w : G.Walk u v, ∀ ⦃x⦄, x ∈ w.support → x ∈ s

@[simp] lemma reachableOn_self (hv : v ∈ s) : G.ReachableOn s v v := ⟨.nil, by simpa⟩

lemma ReachableOn.mono (hst : s ⊆ t) : G.ReachableOn s u v → G.ReachableOn t u v :=
  .imp fun _w ↦ forall_imp fun _x h hx ↦ hst <| h hx

lemma ReachableOn.trans {w : V} :
    G.ReachableOn s u v → G.ReachableOn s v w → G.ReachableOn s u w := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩; exact ⟨p.append q, by simp +contextual [or_imp, *]⟩

lemma ReachableOn.left_mem (hG : G.ReachableOn s u v) : u ∈ s :=
  let ⟨w, hw⟩ := hG; hw w.start_mem_support

lemma ReachableOn.right_mem (hG : G.ReachableOn s u v) : v ∈ s :=
  let ⟨w, hw⟩ := hG; hw w.end_mem_support

protected lemma ReachableOn.deleteEdges {S : Set (Sym2 V)} (hS : ∀ x ∈ s, ∀ y ∈ s, s(x, y) ∉ S) :
    G.ReachableOn s u v → (G.deleteEdges S).ReachableOn s u v := by
  rintro ⟨w, hw⟩
  exact ⟨w.transfer _ <| by
    simp only [Walk.edges, List.mem_map, edgeSet_deleteEdges, Set.mem_sdiff, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, Dart.edge_mem, true_and]
    rintro ⟨⟨x, y⟩, _⟩ hxy
    exact hS _ (hw <| w.dart_fst_mem_support_of_mem_darts hxy) _
      (hw <| w.dart_snd_mem_support_of_mem_darts hxy)
    , by simpa using hw⟩

open scoped Set.Notation
protected lemma ReachableOn.induce (hG : G.ReachableOn t u v) (hts : t ⊆ s) :
    G[s].ReachableOn (s ↓∩ t) ⟨u, hts hG.left_mem⟩ ⟨v, hts hG.right_mem⟩ := by
  obtain ⟨w, hw⟩ := hG
  exact ⟨w.induce _ fun x hx ↦ hts <| hw hx, by simpa using fun x _ hx ↦ hw hx⟩

variable (G s) in
/-- A graph `G` is preconnected on a set `s` if any two vertices of `s` are reachable on `s`. -/
def PreconnectedOn : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → G.ReachableOn s x y

@[simp] lemma preconnectedOn_singleton : G.PreconnectedOn {v} := by simp [PreconnectedOn]

protected lemma PreconnectedOn.deleteEdges {S : Set (Sym2 V)} (hS : ∀ x ∈ s, ∀ y ∈ s, s(x, y) ∉ S)
    (hG : G.PreconnectedOn s) : (G.deleteEdges S).PreconnectedOn s :=
  fun _u hu _v hv ↦ (hG hu hv).deleteEdges hS

variable (G s) in
/-- A graph `G` is connected on a set `s` if `s` is nonempty and any two vertices of `s` are
reachable on `s`. -/
def ConnectedOn : Prop := s.Nonempty ∧ G.PreconnectedOn s

lemma ConnectedOn.nonempty (hG : G.ConnectedOn s) : s.Nonempty := hG.1
lemma ConnectedOn.preconnectedOn (hG : G.ConnectedOn s) : G.PreconnectedOn s := hG.2

@[simp] lemma connectedOn_singleton : G.ConnectedOn {v} := by simp [ConnectedOn]

open scoped Set.Notation
protected lemma PreconnectedOn.induce (hG : G.PreconnectedOn t) (hts : t ⊆ s) :
    G[s].PreconnectedOn (s ↓∩ t) := fun _u hu _v hv ↦ (hG hu hv).induce hts

open scoped Set.Notation
protected lemma ConnectedOn.induce (hG : G.ConnectedOn t) (hts : t ⊆ s) :
    G[s].ConnectedOn (s ↓∩ t) := by
  obtain ⟨x, hx⟩ := hG.nonempty; exact ⟨⟨⟨x, hts hx⟩, by simpa⟩, hG.2.induce hts⟩

protected lemma ConnectedOn.deleteEdges {S : Set (Sym2 V)} (hS : ∀ x ∈ s, ∀ y ∈ s, s(x, y) ∉ S)
    (hG : G.ConnectedOn s) : (G.deleteEdges S).ConnectedOn s :=
  ⟨hG.1, hG.2.deleteEdges hS⟩

/-- The core of a graph `G` is the graph we obtain from `G` after having removed all its bridges. -/
def core (G : SimpleGraph V) : SimpleGraph V := G.deleteEdges {e | G.IsBridge e}

-- TODO: Rename `connectedComponentMk` to `ConnectedComponent.mk`

end SimpleGraph
