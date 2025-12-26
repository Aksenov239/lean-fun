import LeanFun.Coloring.Tmin3_subset_neighborFinset
import LeanFun.Coloring.Tmin3_card

namespace LeanFun.Coloring

theorem auxGraphC3_degree_le_three_mul_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel (auxGraphC3 G).Adj] (v : V) :
    (auxGraphC3 G).degree v ≤ 3 * G.degree v := by
  classical
  let H : SimpleGraph V := auxGraphC3 G
  let Nv : Finset V := H.neighborFinset v
  let Ng : Finset V := G.neighborFinset v
  let f : V → Finset V := fun w =>
    if hv : v ∈ Tmin3 G w then (Tmin3 G w).erase v else ∅

  have hsub : Nv ⊆ Ng ∪ Ng.biUnion f := by
    intro x hx
    have hx' : x ∈ H.neighborFinset v := by
      simpa [Nv] using hx
    have hxAdj : H.Adj v x :=
      (SimpleGraph.mem_neighborFinset (G := H) (v := v) (w := x)).1 hx'
    have hxAdj' :
        G.Adj v x ∨ ∃ w, v ∈ Tmin3 G w ∧ x ∈ Tmin3 G w ∧ v ≠ x := by
      simpa [H, auxGraphC3] using hxAdj
    rcases hxAdj' with hxG | ⟨w, hvw, hxw, hne⟩
    ·
      apply Finset.mem_union.2
      left
      have : x ∈ G.neighborFinset v :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := v) (w := x)).2 hxG
      simpa [Ng] using this
    ·
      apply Finset.mem_union.2
      right
      apply (Finset.mem_biUnion).2
      have hwNg : w ∈ Ng := by
        have hvn : v ∈ G.neighborFinset w :=
          (Tmin3_subset_neighborFinset (G := G) (v := w) hvw)
        have hwvAdj : G.Adj w v :=
          (SimpleGraph.mem_neighborFinset (G := G) (v := w) (w := v)).1 hvn
        have hvwAdj : G.Adj v w := G.symm hwvAdj
        have : w ∈ G.neighborFinset v :=
          (SimpleGraph.mem_neighborFinset (G := G) (v := v) (w := w)).2 hvwAdj
        simpa [Ng] using this
      have hxErase : x ∈ (Tmin3 G w).erase v := by
        exact (Finset.mem_erase).2 ⟨hne.symm, hxw⟩
      have hxFw : x ∈ f w := by
        simpa [f, hvw] using hxErase
      exact ⟨w, hwNg, hxFw⟩

  have hcard1 : Nv.card ≤ Ng.card + (Ng.biUnion f).card := by
    have : Nv.card ≤ (Ng ∪ Ng.biUnion f).card :=
      Finset.card_le_card hsub
    exact le_trans this (Finset.card_union_le Ng (Ng.biUnion f))

  have hcardU : (Ng.biUnion f).card ≤ Ng.card * 2 := by
    classical
    refine Finset.card_biUnion_le_card_mul Ng f 2 ?_
    intro w hw
    by_cases hv : v ∈ Tmin3 G w
    ·
      have hcard : (Tmin3 G w).card ≤ 3 := by
        simpa [Tmin3_card (G := G) (v := w)] using (Nat.min_le_left 3 (G.degree w))
      have hsub : (Tmin3 G w).card - 1 ≤ 2 := by
        have h := Nat.sub_le_sub_right hcard 1
        simpa using h
      have hErase : ((Tmin3 G w).erase v).card ≤ 2 := by
        simpa [Finset.card_erase_of_mem hv] using hsub
      simpa [f, hv] using hErase
    ·
      simp [f, hv]

  have hcard2 : Nv.card ≤ Ng.card + Ng.card * 2 := by
    calc
      Nv.card ≤ Ng.card + (Ng.biUnion f).card := hcard1
      _ ≤ Ng.card + Ng.card * 2 := Nat.add_le_add_left hcardU _

  have hNvdeg : Nv.card = H.degree v := by
    simpa [Nv] using (SimpleGraph.card_neighborFinset_eq_degree (G := H) v)

  have hNgdeg : Ng.card = G.degree v := by
    simpa [Ng] using (SimpleGraph.card_neighborFinset_eq_degree (G := G) v)

  have hdeg : H.degree v ≤ G.degree v + G.degree v * 2 := by
    have : H.degree v ≤ Ng.card + Ng.card * 2 := by
      simpa [hNvdeg] using hcard2
    simpa [hNgdeg] using this

  have harith : G.degree v + G.degree v * 2 = 3 * G.degree v := by
    ring

  have : H.degree v ≤ 3 * G.degree v := by
    simpa [harith] using hdeg

  simpa [H] using this

end LeanFun.Coloring
