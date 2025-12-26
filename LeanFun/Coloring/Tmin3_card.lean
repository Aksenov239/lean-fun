import LeanFun.Coloring.Base

namespace LeanFun.Coloring

theorem Tmin3_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (Tmin3 G v).card = min 3 (G.degree v) := by
  classical
  have h :=
      Classical.choose_spec
        (Finset.exists_subset_card_eq (s := G.neighborFinset v) (n := min 3 (G.degree v))
          (by
            have hcard : (G.neighborFinset v).card = G.degree v := by
              simpa using (SimpleGraph.card_neighborFinset_eq_degree (G := G) v)
            simpa [hcard] using (Nat.min_le_right 3 (G.degree v))))
  simpa [Tmin3] using h.2

end LeanFun.Coloring
