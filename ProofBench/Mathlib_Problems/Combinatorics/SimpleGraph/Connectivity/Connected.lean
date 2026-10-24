module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Maps
public import ProofBench.Mathlib_Problems.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace SimpleGraph
variable {V W : Type*} {G : SimpleGraph V} {s t : Set V} {u u' v w : V}

variable (G s) in
/-- Two vertices `u` and `v` are reachable in a graph `G` on `s` if there exists a walk from `u` to
`v` in `G` whose vertices all lie within `s`. -/
def ReachableOn (u v : V) : Prop := ∃ w : G.Walk u v, ∀ ⦃x⦄, x ∈ w.support → x ∈ s

/-- Every vertex of `s` is reachable from itself on `s`. -/
@[simp] lemma reachableOn_self (hv : v ∈ s) : G.ReachableOn s v v := ⟨.nil, by simpa⟩

/-- Reachability on `s` implies reachability on any superset of `s`. -/
lemma ReachableOn.mono (hst : s ⊆ t) : G.ReachableOn s u v → G.ReachableOn t u v :=
  .imp fun _w ↦ forall_imp fun _x h hx ↦ hst <| h hx

/-- Reachability on `s` is transitive. -/
lemma ReachableOn.trans {w : V} :
    G.ReachableOn s u v → G.ReachableOn s v w → G.ReachableOn s u w := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩; exact ⟨p.append q, by simp +contextual [or_imp, *]⟩

/-- The start of a walk within `s` lies in `s`. -/
lemma ReachableOn.left_mem (hG : G.ReachableOn s u v) : u ∈ s :=
  let ⟨w, hw⟩ := hG; hw w.start_mem_support

/-- The end of a walk within `s` lies in `s`. -/
lemma ReachableOn.right_mem (hG : G.ReachableOn s u v) : v ∈ s :=
  let ⟨w, hw⟩ := hG; hw w.end_mem_support

/-- Deleting edges none of which joins two vertices of `s` preserves reachability on `s`. -/
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
/-- Reachability on `t ⊆ s` transfers to the induced subgraph `G[s]`. -/
protected lemma ReachableOn.induce (hG : G.ReachableOn t u v) (hts : t ⊆ s) :
    G[s].ReachableOn (s ↓∩ t) ⟨u, hts hG.left_mem⟩ ⟨v, hts hG.right_mem⟩ := by
  obtain ⟨w, hw⟩ := hG
  exact ⟨w.induce _ fun x hx ↦ hts <| hw hx, by simpa using fun x _ hx ↦ hw hx⟩

variable (G s) in
/-- A graph `G` is preconnected on a set `s` if any two vertices of `s` are reachable on `s`. -/
def PreconnectedOn : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → G.ReachableOn s x y

/-- Every graph is preconnected on a singleton. -/
@[simp] lemma preconnectedOn_singleton : G.PreconnectedOn {v} := by simp [PreconnectedOn]

/-- Deleting edges none of which joins two vertices of `s` preserves preconnectedness on `s`. -/
protected lemma PreconnectedOn.deleteEdges {S : Set (Sym2 V)} (hS : ∀ x ∈ s, ∀ y ∈ s, s(x, y) ∉ S)
    (hG : G.PreconnectedOn s) : (G.deleteEdges S).PreconnectedOn s :=
  fun _u hu _v hv ↦ (hG hu hv).deleteEdges hS

variable (G s) in
/-- A graph `G` is connected on a set `s` if `s` is nonempty and any two vertices of `s` are
reachable on `s`. -/
def ConnectedOn : Prop := s.Nonempty ∧ G.PreconnectedOn s

/-- A set on which `G` is connected is nonempty. -/
lemma ConnectedOn.nonempty (hG : G.ConnectedOn s) : s.Nonempty := hG.1
/-- Connectedness on `s` implies preconnectedness on `s`. -/
lemma ConnectedOn.preconnectedOn (hG : G.ConnectedOn s) : G.PreconnectedOn s := hG.2

/-- Every graph is connected on a singleton. -/
@[simp] lemma connectedOn_singleton : G.ConnectedOn {v} := by simp [ConnectedOn]

open scoped Set.Notation
/-- Preconnectedness on `t ⊆ s` transfers to the induced subgraph `G[s]`. -/
protected lemma PreconnectedOn.induce (hG : G.PreconnectedOn t) (hts : t ⊆ s) :
    G[s].PreconnectedOn (s ↓∩ t) := fun _u hu _v hv ↦ (hG hu hv).induce hts

open scoped Set.Notation
/-- Connectedness on `t ⊆ s` transfers to the induced subgraph `G[s]`. -/
protected lemma ConnectedOn.induce (hG : G.ConnectedOn t) (hts : t ⊆ s) :
    G[s].ConnectedOn (s ↓∩ t) := by
  obtain ⟨x, hx⟩ := hG.nonempty; exact ⟨⟨⟨x, hts hx⟩, by simpa⟩, hG.2.induce hts⟩

/-- Deleting edges none of which joins two vertices of `s` preserves connectedness on `s`. -/
protected lemma ConnectedOn.deleteEdges {S : Set (Sym2 V)} (hS : ∀ x ∈ s, ∀ y ∈ s, s(x, y) ∉ S)
    (hG : G.ConnectedOn s) : (G.deleteEdges S).ConnectedOn s :=
  ⟨hG.1, hG.2.deleteEdges hS⟩

/-- The core of `G`: the graph obtained from `G` by deleting all its bridges. -/
def core (G : SimpleGraph V) : SimpleGraph V := G.deleteEdges {e | G.IsBridge e}

end SimpleGraph
