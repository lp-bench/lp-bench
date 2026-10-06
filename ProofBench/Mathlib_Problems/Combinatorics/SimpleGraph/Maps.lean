module

public import Mathlib.Combinatorics.SimpleGraph.Maps

public section

namespace SimpleGraph

@[inherit_doc induce]
scoped syntax:max (priority := high) term noWs "[" term "]" : term

macro_rules | `($G[$s]) => `(SimpleGraph.induce $s $G)

/-- Unexpander for `SimpleGraph.induce`. -/
@[scoped app_unexpander SimpleGraph.induce]
meta def unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s $G) => `($G[$s])
  | _ => throw ()

end SimpleGraph
