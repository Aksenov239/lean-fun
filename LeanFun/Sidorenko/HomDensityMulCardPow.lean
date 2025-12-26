import Mathlib
import LeanFun.Sidorenko.Definitions

theorem homDensity_mul_cardPow :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G] [Nonempty V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      homDensity H G * ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) = homCountReal H G := by
  classical
  intro V_H V_G instVH instVG instNE H G
  have hcard_nat : Nat.card V_G ≠ 0 := by
    simpa [Nat.card_eq_fintype_card] using (Fintype.card_ne_zero (α := V_G))
  have hcard : (Nat.card V_G : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hpow : ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) ≠ 0 := by
    exact pow_ne_zero _ hcard
  simpa [homDensity] using (div_mul_cancel₀ (homCountReal H G) hpow)
