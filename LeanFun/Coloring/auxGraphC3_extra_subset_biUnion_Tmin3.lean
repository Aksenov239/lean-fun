import LeanFun.Coloring.Tmin3_subset_neighborFinset
import LeanFun.Coloring.auxGraphC3_adj_of_adj
import LeanFun.Coloring.auxGraphC3_adj_of_mem_Tmin3

namespace LeanFun.Coloring

theorem auxGraphC3_extra_subset_biUnion_Tmin3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel (auxGraphC3 G).Adj]
    {v : V} (s : Finset V) :
    (auxGraphC3 G).neighborFinset v ⊆ s →
      ((auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ⊆
        ((s.filter (fun w => v ∈ Tmin3 G w)).biUnion (fun w => (Tmin3 G w).erase v)) := by
  classical
  intro hsub
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxH, hxnotG⟩
  have hadjHx : (auxGraphC3 G).Adj v x :=
    (SimpleGraph.mem_neighborFinset (G := auxGraphC3 G) (v := v) (w := x)).1 hxH
  have hnotAdj : ¬ G.Adj v x := by
    intro hAdj
    apply hxnotG
    exact (SimpleGraph.mem_neighborFinset (G := G) (v := v) (w := x)).2 hAdj
  rcases hadjHx with hGadj | ⟨w, hvw, hxw, hvx_ne⟩
  · exfalso
    exact hnotAdj hGadj
  ·
    have hv_in_neighbor : v ∈ G.neighborFinset w :=
      (Tmin3_subset_neighborFinset (G := G) (v := w)) hvw
    have hadj_wv : G.Adj w v :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := w) (w := v)).1 hv_in_neighbor
    have hadj_vw : G.Adj v w := G.symm hadj_wv
    have hw_in_H : w ∈ (auxGraphC3 G).neighborFinset v :=
      (SimpleGraph.mem_neighborFinset (G := auxGraphC3 G) (v := v) (w := w)).2 (Or.inl hadj_vw)
    have hw_in_s : w ∈ s := hsub hw_in_H
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨w, ?_, ?_⟩
    ·
      refine Finset.mem_filter.2 ?_
      exact ⟨hw_in_s, hvw⟩
    ·
      refine Finset.mem_erase.2 ?_
      exact ⟨hvx_ne.symm, hxw⟩

end LeanFun.Coloring

