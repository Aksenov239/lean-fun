import LeanFun.Coloring.Base

namespace LeanFun.Coloring

theorem sum_card_filter_Tmin3_eq_sum_card_inter_Tmin3 {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card) =
      ∑ w ∈ s, ((Tmin3 G w ∩ s).card) := by
  classical
  calc
    (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card) =
        ∑ v ∈ s, ∑ w ∈ s, if v ∈ Tmin3 G w then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simpa using (Finset.card_filter (s := s) (p := fun w => v ∈ Tmin3 G w))
    _ = ∑ w ∈ s, ∑ v ∈ s, if v ∈ Tmin3 G w then 1 else 0 := by
      simpa using
        (Finset.sum_comm (s := s) (t := s)
          (f := fun v w => (if v ∈ Tmin3 G w then (1 : ℕ) else 0)))
    _ = ∑ w ∈ s, (s.filter (fun v => v ∈ Tmin3 G w)).card := by
      refine Finset.sum_congr rfl ?_
      intro w hw
      simpa using (Finset.card_filter (s := s) (p := fun v => v ∈ Tmin3 G w)).symm
    _ = ∑ w ∈ s, ((Tmin3 G w ∩ s).card) := by
      refine Finset.sum_congr rfl ?_
      intro w hw
      simpa [Finset.filter_mem_eq_inter, Finset.inter_comm]

end LeanFun.Coloring

