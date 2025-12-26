import Mathlib
import LeanFun.Sidorenko.Defs

open scoped BigOperators

theorem sidorenko_trivial_of_G_edgeless :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      H.edgeSet ≠ ∅ → G.edgeSet = ∅ →
        ((Nat.card (H →g G) : ℝ) ≥ sidorenkoRHS H G) := by
  intro V_H V_G _instH _instG H G hHne hGempty
  classical
  have hL : (0 : ℝ) ≤ (Nat.card (H →g G) : ℝ) := by
    exact_mod_cast (Nat.zero_le (Nat.card (H →g G)))
  have hHpos : 0 < Nat.card (↑H.edgeSet) := by
    have hnonemptySet : Set.Nonempty H.edgeSet := by
      simpa [Set.nonempty_iff_ne_empty] using hHne
    have hnonempty : Nonempty (↑H.edgeSet) := by
      rcases hnonemptySet with ⟨e, he⟩
      exact ⟨⟨e, he⟩⟩
    have hfinite : Finite (↑H.edgeSet) := by
      infer_instance
    exact (Nat.card_pos_iff.mpr ⟨hnonempty, hfinite⟩)
  have hEdgeDensity : edgeDensityK2 G = 0 := by
    simp [edgeDensityK2, hGempty]
  have hRHS : sidorenkoRHS H G = 0 := by
    unfold sidorenkoRHS
    rw [hEdgeDensity]
    have hm : Nat.card (↑H.edgeSet) ≠ 0 := by
      exact ne_of_gt hHpos
    have hpow : (0 : ℝ) ^ (Nat.card (↑H.edgeSet)) = 0 := by
      exact zero_pow hm
    rw [hpow]
    simp
  simpa [hRHS] using hL
