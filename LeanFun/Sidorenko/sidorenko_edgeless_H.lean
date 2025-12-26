import Mathlib
import LeanFun.Sidorenko.Defs
import LeanFun.Sidorenko.card_hom_bot

open scoped BigOperators

theorem sidorenko_edgeless_H :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      H.edgeSet = ∅ →
        ((Nat.card (H →g G) : ℝ) ≥ sidorenkoRHS H G) := by
  intro V_H V_G _ _ H G hH
  have hbot : H = ⊥ := (SimpleGraph.edgeSet_eq_empty (G := H)).1 hH
  subst hbot
  -- simplify RHS
  have hnat := card_hom_bot (V_H := V_H) (V_G := V_G) G
  have hcard : (Nat.card ((⊥ : SimpleGraph V_H) →g G) : ℝ) =
      (Nat.card V_G : ℝ) ^ Nat.card V_H := by
    exact_mod_cast hnat
  -- goal should now be reflexive after simp
  -- simplify goal
  --
  --
  simpa [sidorenkoRHS, edgeDensityK2] using (ge_of_eq hcard)
