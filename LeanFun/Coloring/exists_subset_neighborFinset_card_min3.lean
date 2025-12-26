import LeanFun.Coloring.Base

namespace LeanFun.Coloring

theorem exists_subset_neighborFinset_card_min3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ∃ s : Finset V, s ⊆ G.neighborFinset v ∧ s.card = min 3 (G.degree v) := by
  classical
  let k : ℕ := min 3 (G.degree v)
  have hk : k ≤ (G.neighborFinset v).card := by
    -- `k ≤ G.degree v` and `card neighborFinset = degree`
    simpa [k, SimpleGraph.card_neighborFinset_eq_degree] using (Nat.min_le_right 3 (G.degree v))
  rcases Finset.exists_subset_card_eq hk with ⟨s, hs, hcard⟩
  refine ⟨s, hs, ?_⟩
  simpa [k] using hcard

end LeanFun.Coloring

