import Mathlib
import LeanFun.Sidorenko.Definitions
import LeanFun.Sidorenko.HomCountRealBot

theorem SidorenkoConjecture_homDensity :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G] [Nonempty V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      Nat.card (↑H.edgeSet) = 0 →
        homDensity H G ≥ (globalEdgeDensity (V := V_G) G) ^
          (Nat.card (↑H.edgeSet)) := by
  intro V_H V_G _instH _instG _instN H G hE0
  classical
  -- From `Nat.card` being zero, the edge set is empty.
  have hIsEmpty : IsEmpty (↑H.edgeSet) := by
    -- `Nat.card` is definitionaly `Fintype.card`.
    have hcard : Fintype.card (↑H.edgeSet) = 0 := by
      simpa using hE0
    exact (Fintype.card_eq_zero_iff).1 hcard
  have hempty : H.edgeSet = (∅ : Set (Sym2 V_H)) := by
    ext e
    constructor
    · intro he
      have : False := hIsEmpty.false ⟨e, he⟩
      simpa using this
    · intro he
      simpa using he
  have hbot : H = ⊥ := by
    -- `edgeSet` characterizes the bottom graph.
    exact (SimpleGraph.edgeSet_eq_empty).1 hempty
  subst hbot
  -- Compute the homomorphism density for the empty graph.
  have hcardNat : Nat.card V_G ≠ 0 := by
    simpa using (Fintype.card_ne_zero (α := V_G))
  have hcardV : (Nat.card V_G : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  have hpow : ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) ≠ 0 := by
    exact pow_ne_zero _ hcardV
  have hHD : homDensity (⊥ : SimpleGraph V_H) G = 1 := by
    -- Use the explicit formula for `homCountReal` of `⊥`.
    simp [homDensity, homCountReal_bot, hpow]
  -- Now the inequality is `1 ≥ 1`.
  simpa [hHD, hE0]
