module

public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V} {u u' v w : V}

section DecidableEq
variable [DecidableEq V]

/-- Given a dart in a walk, return the walk up until (and excluding) that dart. -/
@[simp]
def takeUntilDart {v w : V} : ∀ p : G.Walk v w, ∀ e ∈ p.darts, G.Walk v e.fst
  | nil, e, he => by simp at he
  | cons (v := v') hvv' p, e, he =>
    if h : .mk (v, v') hvv' = e then
      h ▸ .nil
    else cons hvv' <| takeUntilDart p e <| by
      cases he
      · exact (h rfl).elim
      · assumption

/-- Given a dart in a walk, return the walk from (and excluding) that dart to the end.
In other words, drop vertices from the front of a walk until (and not including) that dart. -/
@[simp]
def dropUntilDart {v w : V} : ∀ p : G.Walk v w, ∀ e ∈ p.darts, G.Walk e.snd w
  | nil, e, he => by simp at he
  | cons (v := v') hvv' p, e, he =>
    if h : .mk (v, v') hvv' = e then
      h ▸ p
    else dropUntilDart p e <| by
      cases he
      · exact (h rfl).elim
      · assumption

section rotateDart
variable {p : G.Walk v v} {e : G.Dart}

/-- Rotate a loop walk such that it starts with the given dart. -/
def rotateDart (p : G.Walk v v) (e : G.Dart) (he : e ∈ p.darts) : G.Walk e.fst e.fst :=
  .cons e.adj <| (p.dropUntilDart e he).append (p.takeUntilDart e he)

end rotateDart

attribute [simp] bypass

end DecidableEq
end SimpleGraph.Walk
