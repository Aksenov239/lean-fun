import LeanFun.Coloring.Tmin3_subset_neighborFinset
import LeanFun.Coloring.Tmin3_card
import LeanFun.Coloring.Tmin3_erase_card_le_two
import LeanFun.Coloring.auxGraphC3_adj_of_adj
import LeanFun.Coloring.auxGraphC3_adj_of_mem_Tmin3
import LeanFun.Coloring.auxGraphC3_degree_le_three_mul_degree
import LeanFun.Coloring.auxGraphC3_neighborFinset_superset
import LeanFun.Coloring.auxGraphC3_extra_subset_biUnion_Tmin3
import LeanFun.Coloring.sum_card_filter_Tmin3_eq_sum_card_inter_Tmin3

namespace LeanFun.Coloring

theorem auxGraphC3_exists_low_degree_in_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D)
    [DecidableRel (auxGraphC3 G).Adj] :
    ∀ s : Finset V, s.Nonempty →
      ∃ v ∈ s, ((auxGraphC3 G).neighborFinset v ∩ s).card < D * 3 := by
  classical
  intro s hs
  let H : SimpleGraph V := auxGraphC3 G
  let N : ℕ := D * 3
  by_contra hcontra
  push_neg at hcontra
  have hbad : ∀ v : V, v ∈ s → N ≤ ((H.neighborFinset v ∩ s).card) := by
    intro v hv
    simpa [H, N] using (hcontra v hv)

  have hHdeg : ∀ v : V, H.degree v ≤ N := by
    intro v
    have h1 : H.degree v ≤ 3 * G.degree v := by
      simpa [H] using (auxGraphC3_degree_le_three_mul_degree (G := G) (v := v))
    have h2 : 3 * G.degree v ≤ 3 * D := Nat.mul_le_mul_left 3 (hdeg v)
    have h3 : H.degree v ≤ 3 * D := le_trans h1 h2
    simpa [N, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h3

  have hHcard : ∀ v : V, (H.neighborFinset v).card ≤ N := by
    intro v
    have hcard : (H.neighborFinset v).card = H.degree v := by
      simpa using (SimpleGraph.card_neighborFinset_eq_degree (G := H) v)
    -- rewrite the goal using hcard
    -- goal becomes H.degree v ≤ N
    simpa [hcard] using (hHdeg v)

  have hHneighbor_subset : ∀ {v : V}, v ∈ s → H.neighborFinset v ⊆ s := by
    intro v hv
    have hle : N ≤ (H.neighborFinset v ∩ s).card := hbad v hv
    have hEq : H.neighborFinset v ∩ s = H.neighborFinset v := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.inter_subset_left
      · exact le_trans (hHcard v) hle
    exact (Finset.inter_eq_left.mp hEq)

  have hExtra_card : ∀ {v : V}, v ∈ s →
      ((H.neighborFinset v \ G.neighborFinset v).card ≤
        (s.filter (fun w => v ∈ Tmin3 G w)).card * 2) := by
    intro v hv
    have hHs : H.neighborFinset v ⊆ s := hHneighbor_subset (v := v) hv
    have hsubset :=
      auxGraphC3_extra_subset_biUnion_Tmin3 (G := G) (v := v) (s := s) (by simpa [H] using hHs)
    have hcard_le : (H.neighborFinset v \ G.neighborFinset v).card ≤
        ((s.filter (fun w => v ∈ Tmin3 G w)).biUnion (fun w => (Tmin3 G w).erase v)).card :=
      Finset.card_le_card hsubset
    have hbi :
        (((s.filter (fun w => v ∈ Tmin3 G w)).biUnion (fun w => (Tmin3 G w).erase v)).card ≤
          (s.filter (fun w => v ∈ Tmin3 G w)).card * 2) := by
      classical
      simpa using
        (Finset.card_biUnion_le_card_mul (s := s.filter (fun w => v ∈ Tmin3 G w))
          (f := fun w => (Tmin3 G w).erase v) (n := 2)
          (by
            intro w hw
            have hvw : v ∈ Tmin3 G w := (Finset.mem_filter.mp hw).2
            exact Tmin3_erase_card_le_two (G := G) (w := w) (v := v) hvw))
    exact le_trans hcard_le hbi

  have hspos : 0 < s.card := Finset.card_pos.mpr hs

  have hD8 : 8 ≤ D := by
    simpa using hD

  have hDplus6_lt : D + 6 < N := by
    have h2D : 16 ≤ 2 * D := by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using (Nat.mul_le_mul_left 2 hD8)
    have h6lt2D : 6 < 2 * D := lt_of_lt_of_le (by decide : 6 < 16) h2D
    have hlt : D + 6 < D + 2 * D := Nat.add_lt_add_left h6lt2D D
    have hEq : D + 2 * D = N := by
      have : D + 2 * D = D * 3 := by
        ring
      simpa [N] using this
    exact lt_of_lt_of_eq hlt hEq

  have hsum_lower : s.card * N ≤ ∑ v ∈ s, (H.neighborFinset v ∩ s).card := by
    have hsum : (∑ v ∈ s, N) ≤ ∑ v ∈ s, (H.neighborFinset v ∩ s).card := by
      refine Finset.sum_le_sum ?_
      intro v hv
      exact hbad v hv
    simpa using hsum

  have hsum_eq : (∑ v ∈ s, (H.neighborFinset v ∩ s).card) = ∑ v ∈ s, (H.neighborFinset v).card := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hHs : H.neighborFinset v ⊆ s := hHneighbor_subset (v := v) hv
    have hinter : H.neighborFinset v ∩ s = H.neighborFinset v := Finset.inter_eq_left.mpr hHs
    simpa [hinter]

  have hsum_G : (∑ v ∈ s, (G.neighborFinset v).card) ≤ s.card * D := by
    have hle : ∀ v ∈ s, (G.neighborFinset v).card ≤ D := by
      intro v hv
      have hcard : (G.neighborFinset v).card = G.degree v := by
        simpa using (SimpleGraph.card_neighborFinset_eq_degree (G := G) v)
      -- rewrite using hcard
      simpa [hcard] using (hdeg v)
    have hsum : (∑ v ∈ s, (G.neighborFinset v).card) ≤ ∑ v ∈ s, D := by
      refine Finset.sum_le_sum ?_
      intro v hv
      exact hle v hv
    simpa using hsum

  have hsum_extra : (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) ≤ 6 * s.card := by
    have h1 : (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) ≤
        ∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card * 2 := by
      refine Finset.sum_le_sum ?_
      intro v hv
      exact hExtra_card (v := v) hv
    have h1' : (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card * 2) =
        (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card) * 2 := by
      simpa using
        (Finset.sum_mul (s := s)
          (f := fun v => (s.filter (fun w => v ∈ Tmin3 G w)).card) (a := (2 : ℕ))).symm
    have h2 : (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) ≤
        (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card) * 2 := by
      -- rewrite the RHS using h1'
      calc
        (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) ≤
            ∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card * 2 := h1
        _ = (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card) * 2 := h1'

    have hswap : (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card) =
        ∑ w ∈ s, (Tmin3 G w ∩ s).card := by
      simpa using (sum_card_filter_Tmin3_eq_sum_card_inter_Tmin3 (G := G) s)

    have hTmin3_le3 : ∀ w ∈ s, (Tmin3 G w ∩ s).card ≤ 3 := by
      intro w hw
      have hle1 : (Tmin3 G w ∩ s).card ≤ (Tmin3 G w).card :=
        Finset.card_le_card (Finset.inter_subset_left)
      have hle2 : (Tmin3 G w).card ≤ 3 := by
        have hcard : (Tmin3 G w).card = min 3 (G.degree w) := Tmin3_card (G := G) w
        have hmin : min 3 (G.degree w) ≤ 3 := Nat.min_le_left 3 (G.degree w)
        simpa [hcard.symm] using hmin
      exact le_trans hle1 hle2

    have hsumT : (∑ w ∈ s, (Tmin3 G w ∩ s).card) ≤ 3 * s.card := by
      have hsum : (∑ w ∈ s, (Tmin3 G w ∩ s).card) ≤ ∑ w ∈ s, 3 := by
        refine Finset.sum_le_sum ?_
        intro w hw
        exact hTmin3_le3 w hw
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

    have hsumFilter : (∑ v ∈ s, (s.filter (fun w => v ∈ Tmin3 G w)).card) ≤ 3 * s.card := by
      simpa [hswap] using hsumT

    have : (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) ≤ (3 * s.card) * 2 := by
      -- substitute hsumFilter into h2
      exact le_trans h2 (Nat.mul_le_mul_right 2 hsumFilter)

    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this

  have hsum_H : (∑ v ∈ s, (H.neighborFinset v).card) ≤ s.card * (D + 6) := by
    have hsubG : ∀ v : V, G.neighborFinset v ⊆ H.neighborFinset v := by
      intro v
      simpa [H] using (auxGraphC3_neighborFinset_superset (G := G) (v := v))

    have hsplit : ∀ v : V,
        (H.neighborFinset v).card = (H.neighborFinset v \ G.neighborFinset v).card + (G.neighborFinset v).card := by
      intro v
      have h :=
        Finset.card_sdiff_add_card_eq_card (s := G.neighborFinset v) (t := H.neighborFinset v) (hsubG v)
      -- h : (H\G).card + G.card = H.card
      simpa using h.symm

    have hsum_split : (∑ v ∈ s, (H.neighborFinset v).card) =
        (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) +
          ∑ v ∈ s, (G.neighborFinset v).card := by
      classical
      calc
        (∑ v ∈ s, (H.neighborFinset v).card) =
            ∑ v ∈ s, ((H.neighborFinset v \ G.neighborFinset v).card + (G.neighborFinset v).card) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              simpa [hsplit v]
        _ = (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) +
              ∑ v ∈ s, (G.neighborFinset v).card := by
              simpa [Finset.sum_add_distrib]

    have : (∑ v ∈ s, (H.neighborFinset v).card) ≤ s.card * D + 6 * s.card := by
      -- use the split and bounds
      calc
        (∑ v ∈ s, (H.neighborFinset v).card) =
            (∑ v ∈ s, (H.neighborFinset v \ G.neighborFinset v).card) +
              ∑ v ∈ s, (G.neighborFinset v).card := hsum_split
        _ ≤ 6 * s.card + s.card * D := by
              exact Nat.add_le_add hsum_extra hsum_G
        _ = s.card * D + 6 * s.card := by
              ac_rfl

    have hfact : s.card * D + 6 * s.card = s.card * (D + 6) := by
      ring

    exact le_trans this (by simpa [hfact])

  have hsum_upper : (∑ v ∈ s, (H.neighborFinset v ∩ s).card) ≤ s.card * (D + 6) := by
    simpa [hsum_eq] using hsum_H

  have hstrict : s.card * (D + 6) < s.card * N := Nat.mul_lt_mul_of_pos_left hDplus6_lt hspos

  have : (∑ v ∈ s, (H.neighborFinset v ∩ s).card) < s.card * N :=
    lt_of_le_of_lt hsum_upper hstrict

  exact (not_lt_of_ge hsum_lower this)

end LeanFun.Coloring

