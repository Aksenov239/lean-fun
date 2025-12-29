import Mathlib
import LeanFun.Coloring.Tmin3_erase_card_le_two
import LeanFun.Coloring.C3Medium.auxGraphC3_outside_neighbors_card_le_one

namespace LeanFun.Coloring

theorem auxGraphC3_extra_neighbors_in_s_card_bound {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (v : V)
    [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj]
    (hout :
      (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) \ s).card ≤ 1) :
    ((((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card ≤
      (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 2) := by
  classical
  let H : SimpleGraph V := LeanFun.Coloring.auxGraphC3 G
  have hout' : ((H.neighborFinset v) \ s).card ≤ 1 := by
    simpa [H] using hout
  have hTsub :
      ∀ w : V, LeanFun.Coloring.Tmin3 (G := G) w ⊆ G.neighborFinset w := by
    intro w
    classical
    have h :=
      Classical.choose_spec
        (Finset.exists_subset_card_eq (s := G.neighborFinset w)
          (n := min 3 (G.degree w))
          (by
            have hcard : (G.neighborFinset w).card = G.degree w := by
              simpa using
                (SimpleGraph.card_neighborFinset_eq_degree (G := G) w)
            simpa [hcard] using (Nat.min_le_right 3 (G.degree w))))
    simpa [LeanFun.Coloring.Tmin3] using h.1
  let sin : Finset V :=
    s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)
  let sout :
      Finset V :=
        ((H.neighborFinset v) \ s).filter
          (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)
  let Uin : Finset V :=
    sin.biUnion (fun w => (LeanFun.Coloring.Tmin3 (G := G) w).erase v)
  let Uout : Finset V :=
    sout.biUnion (fun w => (LeanFun.Coloring.Tmin3 (G := G) w).erase v)
  have hsub :
      ((H.neighborFinset v \ G.neighborFinset v) ∩ s) ⊆ Uin ∪ Uout := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxExtra, hxS⟩
    rcases Finset.mem_sdiff.mp hxExtra with ⟨hxH, hxnotG⟩
    have hadjHx : H.Adj v x :=
      (SimpleGraph.mem_neighborFinset (G := H) (v := v) (w := x)).1 hxH
    have hnotAdj : ¬ G.Adj v x := by
      intro hAdj
      apply hxnotG
      exact (SimpleGraph.mem_neighborFinset (G := G) (v := v) (w := x)).2 hAdj
    rcases hadjHx with hGadj | ⟨w, hvw, hxw, hvx_ne⟩
    · exact (hnotAdj hGadj).elim
    ·
      by_cases hw : w ∈ s
      ·
        have hw_in : w ∈ sin := by
          have : w ∈ s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w) :=
            Finset.mem_filter.2 ⟨hw, hvw⟩
          simpa [sin] using this
        have hx_erase :
            x ∈ (LeanFun.Coloring.Tmin3 (G := G) w).erase v := by
          refine Finset.mem_erase.2 ?_
          exact ⟨hvx_ne.symm, hxw⟩
        have hx_in : x ∈ Uin := by
          refine (Finset.mem_biUnion).2 ?_
          refine ⟨w, hw_in, ?_⟩
          simpa using hx_erase
        exact Finset.mem_union.2 (Or.inl hx_in)
      ·
        have hv_in_neighbor : v ∈ G.neighborFinset w := (hTsub w) hvw
        have hadj_wv : G.Adj w v :=
          (SimpleGraph.mem_neighborFinset (G := G) (v := w) (w := v)).1 hv_in_neighbor
        have hadj_vw : G.Adj v w := G.symm hadj_wv
        have hw_in_H : w ∈ H.neighborFinset v :=
          (SimpleGraph.mem_neighborFinset (G := H) (v := v) (w := w)).2 (Or.inl hadj_vw)
        have hw_sdiff : w ∈ H.neighborFinset v \ s :=
          Finset.mem_sdiff.2 ⟨hw_in_H, hw⟩
        have hw_out : w ∈ sout := by
          have :
              w ∈ ((H.neighborFinset v \ s).filter
                    (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)) :=
            Finset.mem_filter.2 ⟨hw_sdiff, hvw⟩
          simpa [sout] using this
        have hx_erase :
            x ∈ (LeanFun.Coloring.Tmin3 (G := G) w).erase v := by
          refine Finset.mem_erase.2 ?_
          exact ⟨hvx_ne.symm, hxw⟩
        have hx_out : x ∈ Uout := by
          refine (Finset.mem_biUnion).2 ?_
          refine ⟨w, hw_out, ?_⟩
          simpa using hx_erase
        exact Finset.mem_union.2 (Or.inr hx_out)
  have hUin :
      Uin.card ≤ sin.card * 2 := by
    refine
      Finset.card_biUnion_le_card_mul sin
        (fun w => (LeanFun.Coloring.Tmin3 (G := G) w).erase v) 2 ?_
    intro w hw
    have hw' :
        w ∈ s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w) := by
      simpa [sin] using hw
    have hvw :
        v ∈ LeanFun.Coloring.Tmin3 (G := G) w := (Finset.mem_filter.mp hw').2
    simpa using
      (LeanFun.Coloring.Tmin3_erase_card_le_two (G := G) (w := w) (v := v) hvw)
  have hUout' :
      Uout.card ≤ sout.card * 2 := by
    refine
      Finset.card_biUnion_le_card_mul sout
        (fun w => (LeanFun.Coloring.Tmin3 (G := G) w).erase v) 2 ?_
    intro w hw
    have hw' :
        w ∈ ((H.neighborFinset v \ s).filter
              (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)) := by
      simpa [sout] using hw
    have hvw :
        v ∈ LeanFun.Coloring.Tmin3 (G := G) w := (Finset.mem_filter.mp hw').2
    simpa using
      (LeanFun.Coloring.Tmin3_erase_card_le_two (G := G) (w := w) (v := v) hvw)
  have hsout_card : sout.card ≤ 1 := by
    have hsout_sub : sout ⊆ H.neighborFinset v \ s := by
      intro w hw
      have hw' :
          w ∈ ((H.neighborFinset v \ s).filter
                (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)) := by
        simpa [sout] using hw
      exact (Finset.mem_filter.mp hw').1
    have hsout_le : sout.card ≤ (H.neighborFinset v \ s).card :=
      Finset.card_le_card hsout_sub
    exact le_trans hsout_le hout'
  have hUout : Uout.card ≤ 2 := by
    have hsout_mul : sout.card * 2 ≤ 2 := by
      have : sout.card * 2 ≤ 1 * 2 := Nat.mul_le_mul_right 2 hsout_card
      simpa using this
    exact le_trans hUout' hsout_mul
  have hmain :
      ((H.neighborFinset v \ G.neighborFinset v) ∩ s).card ≤
        sin.card * 2 + 2 := by
    have h1 :
        ((H.neighborFinset v \ G.neighborFinset v) ∩ s).card ≤
          (Uin ∪ Uout).card :=
      Finset.card_le_card hsub
    have h2 :
        (Uin ∪ Uout).card ≤ Uin.card + Uout.card :=
      Finset.card_union_le Uin Uout
    have h3 :
        Uin.card + Uout.card ≤ sin.card * 2 + 2 :=
      Nat.add_le_add hUin hUout
    exact le_trans (le_trans h1 h2) h3
  simpa [H, sin] using hmain

end LeanFun.Coloring

