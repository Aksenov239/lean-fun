import Mathlib
import LeanFun.Sidorenko.Definitions
import LeanFun.Sidorenko.HomDensityMulCardPow
import LeanFun.Sidorenko.SidorenkoConjectureEmptyVG
import LeanFun.Sidorenko.SidorenkoConjectureHomDensity

theorem SidorenkoConjecture_simplified :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      H.IsBipartite → Nat.card (↑H.edgeSet) = 0 →
        homCountReal H G ≥ sidorenkoLowerBound H G := by
  classical
  intro V_H V_G _instH _instG H G hBip hE0
  by_cases hV : IsEmpty V_G
  · haveI : IsEmpty V_G := hV
    simpa using (SidorenkoConjecture_empty_VG (H := H) (G := G))
  · haveI : Nonempty V_G := not_isEmpty_iff.mp hV
    have hHD :
        (globalEdgeDensity (V := V_G) G) ^ (Nat.card (↑H.edgeSet)) ≤ homDensity H G :=
      SidorenkoConjecture_homDensity (H := H) (G := G) hE0
    have hnPow : 0 ≤ ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) := by
      have hcard : 0 ≤ (Nat.card V_G : ℝ) := by
        exact_mod_cast (Nat.zero_le (Nat.card V_G))
      exact pow_nonneg hcard (Nat.card V_H)
    have hmul :
        (globalEdgeDensity (V := V_G) G) ^ (Nat.card (↑H.edgeSet)) *
            ((Nat.card V_G : ℝ) ^ (Nat.card V_H))
          ≤ homDensity H G * ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) :=
      mul_le_mul_of_nonneg_right hHD hnPow
    have hfinal : sidorenkoLowerBound H G ≤ homCountReal H G := by
      calc
        sidorenkoLowerBound H G =
            (globalEdgeDensity (V := V_G) G) ^ (Nat.card (↑H.edgeSet)) *
              ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) := by
              rfl
        _ ≤ homDensity H G * ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) := hmul
        _ = homCountReal H G := by
            simpa using (homDensity_mul_cardPow (H := H) (G := G))
    exact hfinal
