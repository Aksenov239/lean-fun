import Mathlib
import LeanFun.Sidorenko.Definitions

theorem SidorenkoConjecture_empty_VG :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G] [IsEmpty V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      homCountReal H G ≥ sidorenkoLowerBound H G := by
  intro V_H V_G _instH _instG _instE H G
  classical
  by_cases hVH : IsEmpty V_H
  ·
    letI : IsEmpty V_H := hVH
    -- In this case there is a unique homomorphism from `H`.
    simp [homCountReal, sidorenkoLowerBound, globalEdgeDensity]
  ·
    haveI : Nonempty V_H := (not_isEmpty_iff.mp hVH)
    -- No map from a nonempty type to an empty type, hence no homomorphisms.
    haveI : IsEmpty (H →g G) := by
      refine ⟨?_⟩
      intro f
      classical
      obtain ⟨v⟩ := ‹Nonempty V_H›
      exact (IsEmpty.false (f v))
    have hne : Nat.card V_H ≠ 0 := by
      -- `V_H` is nonempty.
      have : 0 < Fintype.card V_H := Fintype.card_pos_iff.mpr ‹Nonempty V_H›
      -- Switch to `Nat.card`.
      simpa [Nat.card_eq_fintype_card, Nat.pos_iff_ne_zero] using this
    have hpow : ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) = 0 := by
      -- `Nat.card V_G = 0` since `V_G` is empty.
      simp [zero_pow hne]
    -- Both sides are `0`.
    simp [homCountReal, sidorenkoLowerBound, globalEdgeDensity, hpow]
