import Mathlib
import LeanFun.Coloring.sum_card_filter_Tmin3_eq_sum_card_inter_Tmin3
import LeanFun.Coloring.Tmin3_card
import LeanFun.Coloring.C3Medium.auxGraphC3_outside_neighbors_card_le_one
import LeanFun.Coloring.C3Medium.auxGraphC3_extra_neighbors_in_s_card_bound

namespace LeanFun.Coloring

theorem auxGraphC3_sum_extra_neighbors_in_s_le {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdeg : ∀ v : V, G.degree v ≤ D)
    [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj]
    (s : Finset V)
    (hbig :
      ∀ v ∈ s,
        D * 3 - 1 ≤ (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) ∩ s).card) :
    (∑ v ∈ s,
        ((((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card)) ≤
      8 * s.card := by
  classical
  let H : SimpleGraph V := LeanFun.Coloring.auxGraphC3 G
  have hle :
      (∑ v ∈ s,
          ((((H.neighborFinset v \ G.neighborFinset v) ∩ s).card))) ≤
        ∑ v ∈ s,
          ((s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 2) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    have hout :
        (((H.neighborFinset v) \ s).card ≤ 1) := by
      apply
        auxGraphC3_outside_neighbors_card_le_one (G := G) (D := D) (hdeg := hdeg)
          (s := s) (v := v)
      exact hbig v hv
    exact
      auxGraphC3_extra_neighbors_in_s_card_bound (G := G) (s := s) (v := v)
        (hout := hout)
  have hsum_filter :
      (∑ v ∈ s,
          (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) ≤
        3 * s.card := by
    calc
      (∑ v ∈ s,
          (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) =
          ∑ w ∈ s, ((LeanFun.Coloring.Tmin3 (G := G) w ∩ s).card) := by
        simpa using
          (LeanFun.Coloring.sum_card_filter_Tmin3_eq_sum_card_inter_Tmin3
            (G := G) (s := s))
      _ ≤ ∑ w ∈ s, 3 := by
        refine Finset.sum_le_sum ?_
        intro w hw
        have hinter :
            ((LeanFun.Coloring.Tmin3 (G := G) w ∩ s).card) ≤
              (LeanFun.Coloring.Tmin3 (G := G) w).card := by
          exact Finset.card_le_card Finset.inter_subset_left
        have htmin :
            (LeanFun.Coloring.Tmin3 (G := G) w).card ≤ 3 := by
          have hcard := LeanFun.Coloring.Tmin3_card (G := G) w
          have hmin : min 3 (G.degree w) ≤ 3 :=
            Nat.min_le_left 3 (G.degree w)
          simpa [hcard] using hmin
        exact le_trans hinter htmin
      _ = 3 * s.card := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hRHS :
      (∑ v ∈ s,
          ((s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 2)) ≤
        8 * s.card := by
    have hmul :
        (∑ v ∈ s,
            (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) * 2 =
          ∑ v ∈ s,
            (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 := by
      simpa using
        (Finset.sum_mul (s := s)
          (f := fun v =>
            (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card)
          (a := (2 : ℕ)))
    have hmul_le :
        (∑ v ∈ s,
            (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) * 2 ≤
          (3 * s.card) * 2 :=
      Nat.mul_le_mul_right 2 hsum_filter
    calc
      (∑ v ∈ s,
            ((s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2 + 2)) =
          (∑ v ∈ s,
              (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card * 2) +
            ∑ v ∈ s, 2 := by
        simp [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
      _ =
          ((∑ v ∈ s,
                  (s.filter (fun w => v ∈ LeanFun.Coloring.Tmin3 (G := G) w)).card) * 2) +
            (2 * s.card) := by
        rw [← hmul]
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ ((3 * s.card) * 2) + (2 * s.card) := by
        exact Nat.add_le_add_right hmul_le (2 * s.card)
      _ = 8 * s.card := by
        ring
  exact le_trans hle hRHS

end LeanFun.Coloring
