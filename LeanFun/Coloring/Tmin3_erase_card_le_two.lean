import LeanFun.Coloring.Tmin3_card

namespace LeanFun.Coloring

theorem Tmin3_erase_card_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w v : V} :
    v ∈ Tmin3 G w → ((Tmin3 G w).erase v).card ≤ 2 := by
  intro hv
  have hcard : (Tmin3 G w).card ≤ 3 := by
    simpa [Tmin3_card] using (Nat.min_le_left 3 (G.degree w))
  have hsub : (Tmin3 G w).card - 1 ≤ 2 := by
    have h := Nat.sub_le_sub_right hcard 1
    simpa using h
  simpa [Finset.card_erase_of_mem hv] using hsub

end LeanFun.Coloring
