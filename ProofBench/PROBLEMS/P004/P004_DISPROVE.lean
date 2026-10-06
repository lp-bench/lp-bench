/-
Prove-or-disprove companion — DISPROVE polarity for P004 (Sidorenko's
conjecture for bipartite graphs).
-/
import ProofBench.PROBLEMS.P004.P004

/-- **Disprove version of P004.**  The negation of Sidorenko's conjecture for
bipartite graphs: some bipartite graph `H` and some nonempty finite host `G`
violate `t(H, G) ≥ t(K₂, G)^{e(H)}`.

The prove polarity is an open conjecture, so it is genuinely unknown which of
the two polarities is provable; establishing this one would refute
Sidorenko's conjecture. -/
theorem P004_disprove :
    ¬ ∀ (W V : Type) [Fintype W] [Fintype V] [Nonempty V]
        (H : SimpleGraph W) (G : SimpleGraph V) (X Y : Set W),
        H.IsBipartiteWith X Y → SidorenkoFor H G := by
  sorry
