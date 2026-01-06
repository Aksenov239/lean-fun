import Mathlib
import LeanFun.Coloring.Base
import LeanFun.Coloring.Tmin3_erase_card_le_two
import LeanFun.Coloring.C3Medium.auxGraphC3_neighborFinset_card_le_three_mul_D
import LeanFun.Coloring.sum_card_filter_Tmin3_eq_sum_card_inter_Tmin3
import LeanFun.Coloring.Tmin3_card
import LeanFun.Coloring.SimpleGraph_colorable_of_forall_finset_exists_degree_lt
import LeanFun.Coloring.auxGraphC3_adj_of_adj
import LeanFun.Coloring.auxGraphC3_neighbor_image_card_ge_min3
import LeanFun.Coloring.ColorOfFin
import LeanFun.Coloring.C3Medium.colorOfFin_injective
import LeanFun.Coloring.C3Medium.card_image_colorOfFin_comp

open scoped BigOperators

-- theorem exists_coloring_c3_simple
--     {V : Type*} [Fintype V] [DecidableEq V]
--     (G : SimpleGraph V) [DecidableRel G.Adj]
--     (D : ℕ)
--     (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
--     (hdeg : ∀ v : V, G.degree v ≤ D) :
--     let c : ℕ := 3
--     let N : ℕ := D * c
--     ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
--       (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
--       (∀ v : V,
--         let k : ℕ := min c (G.degree v)
--         let s := G.neighborFinset v
--         (s.image (fun x => f x)).card >= k) :=
--   -- proof goes here
--   sorry

theorem exists_coloring_c3
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * 2 + 1
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        ∃ s : Finset V,
          s ⊆ G.neighborFinset v ∧
          s.card = k ∧
          (s.image (fun x => f x)).card = k) :=
  -- proof goes here
  sorry

theorem exists_coloring_c4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (4 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 4
    let N : ℕ := D * (c - 1) + 1
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        ∃ s : Finset V,
          s ⊆ G.neighborFinset v ∧
          s.card = k ∧
          (s.image (fun x => f x)).card = k) :=
  -- proof goes here
  sorry

open LeanFun.Coloring

theorem auxGraphC3_extra_neighbors_in_s_card_bound_v3 {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (s : Finset V) (v : V)
  [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj]
  (hout : ((((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) \ s).card ≤ 2)) :
  ((((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card ≤
    (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 4) := by
  classical
  let H : SimpleGraph V := LeanFun.Coloring.auxGraphC3 G
  have hout' : ((H.neighborFinset v) \ s).card ≤ 2 := by
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
              simpa using (SimpleGraph.card_neighborFinset_eq_degree (G := G) w)
            simpa [hcard] using (Nat.min_le_right 3 (G.degree w))))
    simpa [LeanFun.Coloring.Tmin3] using h.1
  let sin : Finset V :=
    s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)
  let sout : Finset V :=
    ((H.neighborFinset v) \ s).filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)
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
        have hx_erase : x ∈ (LeanFun.Coloring.Tmin3 (G := G) w).erase v := by
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
        have hx_erase : x ∈ (LeanFun.Coloring.Tmin3 (G := G) w).erase v := by
          refine Finset.mem_erase.2 ?_
          exact ⟨hvx_ne.symm, hxw⟩
        have hx_out : x ∈ Uout := by
          refine (Finset.mem_biUnion).2 ?_
          refine ⟨w, hw_out, ?_⟩
          simpa using hx_erase
        exact Finset.mem_union.2 (Or.inr hx_out)
  have hUin : Uin.card ≤ sin.card * 2 := by
    refine
      Finset.card_biUnion_le_card_mul sin
        (fun w => (LeanFun.Coloring.Tmin3 (G := G) w).erase v) 2 ?_
    intro w hw
    have hw' :
        w ∈ s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w) := by
      simpa [sin] using hw
    have hvw : v ∈ LeanFun.Coloring.Tmin3 (G := G) w := (Finset.mem_filter.mp hw').2
    simpa using
      (LeanFun.Coloring.Tmin3_erase_card_le_two (G := G) (w := w) (v := v) hvw)
  have hUout' : Uout.card ≤ sout.card * 2 := by
    refine
      Finset.card_biUnion_le_card_mul sout
        (fun w => (LeanFun.Coloring.Tmin3 (G := G) w).erase v) 2 ?_
    intro w hw
    have hw' :
        w ∈ ((H.neighborFinset v \ s).filter
              (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)) := by
      simpa [sout] using hw
    have hvw : v ∈ LeanFun.Coloring.Tmin3 (G := G) w := (Finset.mem_filter.mp hw').2
    simpa using
      (LeanFun.Coloring.Tmin3_erase_card_le_two (G := G) (w := w) (v := v) hvw)
  have hsout_card : sout.card ≤ 2 := by
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
  have hUout : Uout.card ≤ 4 := by
    have hsout_mul : sout.card * 2 ≤ 4 := by
      have : sout.card * 2 ≤ 2 * 2 := Nat.mul_le_mul_right 2 hsout_card
      simpa using this
    exact le_trans hUout' hsout_mul
  have hmain :
      ((H.neighborFinset v \ G.neighborFinset v) ∩ s).card ≤
        sin.card * 2 + 4 := by
    have h1 :
        ((H.neighborFinset v \ G.neighborFinset v) ∩ s).card ≤
          (Uin ∪ Uout).card :=
      Finset.card_le_card hsub
    have h2 : (Uin ∪ Uout).card ≤ Uin.card + Uout.card :=
      Finset.card_union_le Uin Uout
    have h3 : Uin.card + Uout.card ≤ sin.card * 2 + 4 :=
      Nat.add_le_add hUin hUout
    exact le_trans (le_trans h1 h2) h3
  simpa [H, sin] using hmain

theorem auxGraphC3_outside_neighbors_card_le_two {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (D : ℕ) (hdeg : ∀ v : V, G.degree v ≤ D)
  [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj]
  (s : Finset V) (v : V)
  (hbig : D * 3 - 2 ≤ (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) ∩ s).card) :
  ((((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) \ s).card ≤ 2) := by
  classical
  let H := LeanFun.Coloring.auxGraphC3 G
  have hH : (H.neighborFinset v).card ≤ D * 3 := by
    simpa [H] using
      (auxGraphC3_neighborFinset_card_le_three_mul_D (G := G) (D := D) hdeg (v := v))
  have hcard :
      ((H.neighborFinset v) \ s).card =
        (H.neighborFinset v).card - (s ∩ H.neighborFinset v).card := by
    simpa [H] using (Finset.card_sdiff (s := s) (t := H.neighborFinset v))
  have hbig' : D * 3 - 2 ≤ (s ∩ H.neighborFinset v).card := by
    simpa [Finset.inter_comm, H] using hbig
  rw [hcard]
  have h2 :
      (H.neighborFinset v).card - (s ∩ H.neighborFinset v).card ≤
        (H.neighborFinset v).card - (D * 3 - 2) := by
    exact Nat.sub_le_sub_left hbig' (H.neighborFinset v).card
  have h3 :
      (H.neighborFinset v).card - (D * 3 - 2) ≤ D * 3 - (D * 3 - 2) := by
    exact Nat.sub_le_sub_right hH (D * 3 - 2)
  have h4 : D * 3 - (D * 3 - 2) ≤ 2 := by
    cases h : D * 3 with
    | zero =>
        simp [h]
    | succ n =>
        cases n with
        | zero =>
            simp [h]
        | succ m =>
            -- D * 3 = m + 2
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (show m + 1 + 1 ≤ 2 + m from by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])
  exact le_trans (le_trans h2 h3) h4

theorem sum_card_filter_Tmin3_le_three_mul_card {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (s : Finset V) :
  (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) ≤ 3 * s.card := by
  classical
  -- Swap the order of summation using the provided lemma
  have hswap :
      (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) =
        ∑ w ∈ s, ((LeanFun.Coloring.Tmin3 (G := G) w ∩ s).card) := by
    simpa using (sum_card_filter_Tmin3_eq_sum_card_inter_Tmin3 (G := G) (s := s))
  -- Rewrite and bound termwise by 3
  rw [hswap]
  have hterm :
      ∀ w ∈ s, ((LeanFun.Coloring.Tmin3 (G := G) w ∩ s).card) ≤ (3 : ℕ) := by
    intro w hw
    have hinter :
        ((LeanFun.Coloring.Tmin3 (G := G) w ∩ s).card) ≤
          (LeanFun.Coloring.Tmin3 (G := G) w).card := by
      exact Finset.card_le_card (Finset.inter_subset_left)
    have hT : (LeanFun.Coloring.Tmin3 (G := G) w).card ≤ (3 : ℕ) := by
      -- `Tmin3_card` computes the size of `Tmin3` as `min 3 (degree w)`.
      -- Then `min 3 (degree w) ≤ 3`.
      simpa [Tmin3_card (G := G) w] using (Nat.min_le_left 3 (G.degree w))
    exact le_trans hinter hT
  calc
      (∑ w ∈ s, ((LeanFun.Coloring.Tmin3 (G := G) w ∩ s).card))
          ≤ ∑ w ∈ s, (3 : ℕ) := by
            exact Finset.sum_le_sum hterm
      _ = 3 * s.card := by
            -- `simp` turns the sum of a constant into `s.card * 3`; commute factors.
            simp [Nat.mul_comm]

theorem auxGraphC3_sum_extra_neighbors_in_s_le_v3 {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (D : ℕ) (hdeg : ∀ v : V, G.degree v ≤ D)
  [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj]
  (s : Finset V)
  (hbig : ∀ v ∈ s,
    D * 3 - 2 ≤ (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) ∩ s).card) :
  (∑ v ∈ s,
      (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card) ≤
    10 * s.card := by
  classical

  -- Pointwise bound.
  have hterm :
      ∀ v ∈ s,
        ((((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card ≤
          (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 4) := by
    intro v hv
    have hout : ((((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) \ s).card ≤ 2) := by
      exact
        auxGraphC3_outside_neighbors_card_le_two (G := G) (D := D) (hdeg := hdeg) (s := s) (v := v)
          (hbig := hbig v hv)
    exact
      auxGraphC3_extra_neighbors_in_s_card_bound_v3 (G := G) (s := s) (v := v) (hout := hout)

  have hsum :
      (∑ v ∈ s,
          (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card) ≤
        (∑ v ∈ s,
          ((s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 4)) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact hterm v hv

  -- Rewrite the RHS sum.
  have hsum_rw :
      (∑ v ∈ s,
          ((s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 4)) =
        (2 * (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) +
            4 * s.card) := by
    -- split the sum and factor out constants
    calc
      (∑ v ∈ s,
            ((s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 4))
          = (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2) +
              (∑ _v ∈ s, 4) := by
                simp [Finset.sum_add_distrib]
      _ = (2 * (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card)) +
              (s.card * 4) := by
                -- first term
                simp [Finset.mul_sum, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = 2 * (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) +
              4 * s.card := by
                ring_nf

  have hfilter_le :
      (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) ≤
        3 * s.card := by
    simpa using sum_card_filter_Tmin3_le_three_mul_card (G := G) (s := s)

  -- Finish.
  calc
    (∑ v ∈ s,
        (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card)
        ≤ (∑ v ∈ s,
            ((s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 4)) :=
          hsum
    _ = 2 * (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) +
            4 * s.card := by
          simpa [hsum_rw]
    _ ≤ 2 * (3 * s.card) + 4 * s.card := by
          -- multiply the bound by 2 and add the constant term
          have hmul :
              2 * (∑ v ∈ s, (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) ≤
                2 * (3 * s.card) := by
            exact Nat.mul_le_mul_left 2 hfilter_le
          exact Nat.add_le_add_right hmul (4 * s.card)
    _ = 10 * s.card := by
          ring


theorem auxGraphC3_exists_low_degree_in_induce_v3 {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (D : ℕ) (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
  (hdeg : ∀ v : V, G.degree v ≤ D)
  [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj] :
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) ∩ s).card < D * 3 - 2 := by
  intro s hs
  classical
  let H : SimpleGraph V := LeanFun.Coloring.auxGraphC3 G
  let N : ℕ := D * 3 - 2
  by_contra hno
  have hbig :
      ∀ v ∈ s, N ≤ ((H.neighborFinset v) ∩ s).card := by
    intro v hv
    by_contra hNv
    apply hno
    refine ⟨v, hv, ?_⟩
    have : ((H.neighborFinset v) ∩ s).card < N := lt_of_not_ge hNv
    simpa [H, N] using this
  have hLower :
      s.card * N ≤ ∑ v ∈ s, ((H.neighborFinset v) ∩ s).card := by
    calc
      s.card * N = ∑ _v ∈ s, N := by simp [N]
      _ ≤ ∑ v ∈ s, ((H.neighborFinset v) ∩ s).card := by
        refine Finset.sum_le_sum ?_
        intro v hv
        exact hbig v hv
  have hCard_le :
      ∀ v ∈ s,
        ((H.neighborFinset v) ∩ s).card ≤
          (G.neighborFinset v).card +
            (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card) := by
    intro v hv
    have hsubset :
        (H.neighborFinset v ∩ s) ⊆
          (G.neighborFinset v ∪
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s)) := by
      intro x hx
      have hxH :
          x ∈ H.neighborFinset v := (Finset.mem_inter.1 hx).1
      have hxS : x ∈ s := (Finset.mem_inter.1 hx).2
      by_cases hxG : x ∈ G.neighborFinset v
      · exact Finset.mem_union.2 (Or.inl hxG)
      ·
        have hxDiff : x ∈ (H.neighborFinset v \ G.neighborFinset v) := by
          exact Finset.mem_sdiff.2 ⟨hxH, hxG⟩
        have hxExtra :
            x ∈ ((H.neighborFinset v \ G.neighborFinset v) ∩ s) := by
          exact Finset.mem_inter.2 ⟨hxDiff, hxS⟩
        exact Finset.mem_union.2 (Or.inr hxExtra)
    have h1 :
        ((H.neighborFinset v) ∩ s).card ≤
          (G.neighborFinset v ∪
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s)).card :=
      Finset.card_le_card hsubset
    have h2 :
        (G.neighborFinset v ∪
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s)).card ≤
          (G.neighborFinset v).card +
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s).card := by
      simpa using
        (Finset.card_union_le (G.neighborFinset v)
          ((H.neighborFinset v \ G.neighborFinset v) ∩ s))
    exact le_trans h1 h2
  have hUpper :
      (∑ v ∈ s, ((H.neighborFinset v) ∩ s).card) ≤ s.card * (D + 10) := by
    have hSum_le :
        (∑ v ∈ s, ((H.neighborFinset v) ∩ s).card) ≤
          ∑ v ∈ s,
            ((G.neighborFinset v).card +
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) := by
      refine Finset.sum_le_sum ?_
      intro v hv
      exact hCard_le v hv
    have hSum_le' :
        (∑ v ∈ s, ((H.neighborFinset v) ∩ s).card) ≤
          (∑ v ∈ s, (G.neighborFinset v).card) +
            (∑ v ∈ s,
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) := by
      simpa [Finset.sum_add_distrib] using hSum_le
    have hSumG :
        (∑ v ∈ s, (G.neighborFinset v).card) ≤ s.card * D := by
      have hSumG' :
          (∑ v ∈ s, (G.neighborFinset v).card) ≤ ∑ _v ∈ s, D := by
        refine Finset.sum_le_sum ?_
        intro v hv
        calc
          (G.neighborFinset v).card = G.degree v := by
            simpa using
              (SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v))
          _ ≤ D := hdeg v
      simpa using hSumG'
    have hSumExtra :
        (∑ v ∈ s,
            (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) ≤
          10 * s.card := by
      have h' :
          (∑ v ∈ s,
              (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card) ≤
            10 * s.card :=
        auxGraphC3_sum_extra_neighbors_in_s_le_v3 (G := G) (D := D) (hdeg := hdeg)
          (s := s)
          (hbig :=
            by
              intro v hv
              simpa [H, N] using hbig v hv)
      simpa [H] using h'
    have hSumTotal :
        (∑ v ∈ s, (G.neighborFinset v).card) +
            (∑ v ∈ s,
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) ≤
          s.card * D + 10 * s.card :=
      add_le_add hSumG hSumExtra
    have hSumTotal' :
        (∑ v ∈ s, (G.neighborFinset v).card) +
            (∑ v ∈ s,
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) ≤
          s.card * (D + 10) := by
      simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSumTotal
    exact le_trans hSum_le' hSumTotal'
  have hD8 : 8 ≤ D := by
    simpa using hD
  have hspos : 0 < s.card := by
    exact (Finset.card_pos.2 hs)
  have hDpluslt : D + 10 < N := by
    have h16le2D : 16 ≤ 2 * D := by
      have := Nat.mul_le_mul_left 2 hD8
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
    have h12lt16 : 12 < 16 := by decide
    have h12lt2D : 12 < 2 * D := lt_of_lt_of_le h12lt16 h16le2D
    have hD12ltD2D : D + 12 < D + 2 * D := Nat.add_lt_add_left h12lt2D D
    have hD12lt3D : D + 12 < D * 3 := by
      have hEq : D + 2 * D = D * 3 := by ring
      exact lt_of_lt_of_eq hD12ltD2D hEq
    have hAdd : D + 10 + 2 < D * 3 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hD12lt3D
    have : D + 10 < D * 3 - 2 := lt_tsub_of_add_lt_right hAdd
    simpa [N] using this
  have hMul_lt : s.card * (D + 10) < s.card * N :=
    Nat.mul_lt_mul_of_pos_left hDpluslt hspos
  have hLe : s.card * N ≤ s.card * (D + 10) :=
    le_trans hLower hUpper
  exact (not_lt_of_ge hLe) hMul_lt

theorem auxGraphC3_colorable_v3 {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (D : ℕ) (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
  (hdeg : ∀ v : V, G.degree v ≤ D) :
  (LeanFun.Coloring.auxGraphC3 G).Colorable (D * 3 - 2) := by
  classical
  let H := LeanFun.Coloring.auxGraphC3 G
  haveI : DecidableRel H.Adj := by
    classical
    exact Classical.decRel _
  simpa [H] using
    (LeanFun.Coloring.SimpleGraph_colorable_of_forall_finset_exists_degree_lt
      (G := H) (n := D * 3 - 2)
      (auxGraphC3_exists_low_degree_in_induce_v3 (G := G) (D := D) hD hdeg))

theorem exists_coloring_c3_v3_fin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * c - 2
    ∃ g : V → Fin N,
      (∀ ⦃u v : V⦄, G.Adj u v → g u ≠ g v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        let s := G.neighborFinset v
        (s.image g).card ≥ k) := by
  classical
  simp (config := { zeta := true })
  have hc : (LeanFun.Coloring.auxGraphC3 G).Colorable (D * 3 - 2) :=
    auxGraphC3_colorable_v3 (G := G) (D := D) (hD := hD) (hdeg := hdeg)
  rcases hc with ⟨C⟩
  refine ⟨C, ?_, ?_⟩
  · intro u v huv
    have : (LeanFun.Coloring.auxGraphC3 G).Adj u v :=
      LeanFun.Coloring.auxGraphC3_adj_of_adj (G := G) huv
    exact C.valid this
  · intro v
    simp (config := { zeta := true })
    have hN : D * 3 - 2 ≤ D * 3 := by
      exact Nat.sub_le (D * 3) 2
    let emb : Fin (D * 3 - 2) ↪ Fin (D * 3) := Fin.castLEEmb hN
    let f : V → Fin (D * 3) := fun x => emb (C x)
    have hfproper :
        ∀ ⦃u v : V⦄, (LeanFun.Coloring.auxGraphC3 G).Adj u v → f u ≠ f v := by
      intro u v huv hEq
      apply (C.valid huv)
      exact emb.injective hEq
    have hneigh_f :
        ((G.neighborFinset v).image f).card ≥ min 3 (G.degree v) := by
      have hAll :=
        LeanFun.Coloring.auxGraphC3_neighbor_image_card_ge_min3 (G := G) (D := D) (hdeg := hdeg)
      simpa [f] using (hAll f hfproper v)
    have himage :
        ((G.neighborFinset v).image C).image emb =
          (G.neighborFinset v).image f := by
      simpa [f, Function.comp] using
        (Finset.image_image (s := G.neighborFinset v) (f := C) (g := emb))
    have hcard :
        ((G.neighborFinset v).image f).card =
          ((G.neighborFinset v).image C).card := by
      calc
        ((G.neighborFinset v).image f).card =
            (((G.neighborFinset v).image C).image emb).card := by
          simpa [himage]
        _ = ((G.neighborFinset v).image C).card := by
          simpa using
            (Finset.card_image_of_injective ((G.neighborFinset v).image C)
              emb.injective)
    simpa [hcard] using hneigh_f

theorem exists_coloring_c3_v3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * 3 - 2
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        ∃ s : Finset V,
        let s := G.neighborFinset v
        (s.image (fun x => f x)).card >= k) := by
  classical
  -- Unfold the top-level `let` bindings (`c = 3`, `N = D * 3 - 2`).
  dsimp
  -- Obtain a coloring into `Fin (D * 3 - 2)` with the required properties.
  have hfin :=
    exists_coloring_c3_v3_fin (V := V) (G := G) (D := D) hD hdeg
  dsimp at hfin
  rcases hfin with ⟨g, hgProper, hgCard⟩
  -- Convert the `Fin`-coloring to a coloring into `{n : ℕ // n ∈ Set.Icc 1 N}`.
  let f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) (D * 3 - 2)} :=
    fun v => LeanFun.Coloring.colorOfFin (D * 3 - 2) (g v)
  refine ⟨f, ?_, ?_⟩
  · intro u v huv hfv
    have hgv : g u = g v :=
      (LeanFun.Coloring.colorOfFin_injective (N := (D * 3 - 2))) hfv
    exact (hgProper huv) hgv
  · intro v
    refine ⟨∅, ?_⟩
    -- The existential witness is unused due to the shadowing `let s := ...`.
    -- Rewrite the card of the image under `f` as the card of the image under `g`.
    have hcard_comp :
        ((G.neighborFinset v).image (fun x => f x)).card =
          ((G.neighborFinset v).image g).card := by
      simpa [f] using
        (Finset.card_image_colorOfFin_comp
          (N := (D * 3 - 2)) (s := G.neighborFinset v) (g := g))
    have hgCard' : ((G.neighborFinset v).image g).card ≥ min 3 (G.degree v) := by
      simpa using (hgCard v)
    simpa [hcard_comp] using hgCard'
