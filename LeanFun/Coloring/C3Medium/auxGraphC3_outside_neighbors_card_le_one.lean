import Mathlib
import LeanFun.Coloring.C3Medium.auxGraphC3_neighborFinset_card_le_three_mul_D

namespace LeanFun.Coloring

theorem auxGraphC3_outside_neighbors_card_le_one {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdeg : ∀ v : V, G.degree v ≤ D)
    [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj]
    (s : Finset V) (v : V)
    (hbig :
      D * 3 - 1 ≤ (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) ∩ s).card) :
    (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) \ s).card ≤ 1 := by
  classical
  let H := LeanFun.Coloring.auxGraphC3 G
  have hH : (H.neighborFinset v).card ≤ D * 3 := by
    simpa [H] using
      (auxGraphC3_neighborFinset_card_le_three_mul_D (G := G) (D := D) hdeg
        (v := v))
  have hcard :
      ((H.neighborFinset v) \ s).card =
        (H.neighborFinset v).card - (s ∩ H.neighborFinset v).card := by
    simpa [H] using (Finset.card_sdiff (s := s) (t := H.neighborFinset v))
  have hbig' :
      D * 3 - 1 ≤ (s ∩ H.neighborFinset v).card := by
    simpa [Finset.inter_comm, H] using hbig
  rw [hcard]
  have h2 :
      (H.neighborFinset v).card - (s ∩ H.neighborFinset v).card ≤
        (H.neighborFinset v).card - (D * 3 - 1) := by
    exact Nat.sub_le_sub_left hbig' (H.neighborFinset v).card
  have h3 :
      (H.neighborFinset v).card - (D * 3 - 1) ≤ D * 3 - (D * 3 - 1) := by
    exact Nat.sub_le_sub_right hH (D * 3 - 1)
  have h4 : D * 3 - (D * 3 - 1) ≤ 1 := by
    cases h : D * 3 with
    | zero => simp [h]
    | succ n => simp [h]
  exact le_trans (le_trans h2 h3) h4

end LeanFun.Coloring

