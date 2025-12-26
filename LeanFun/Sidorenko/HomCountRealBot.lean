import Mathlib
import LeanFun.Sidorenko.Definitions

theorem homCountReal_bot :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
      (G : SimpleGraph V_G),
      homCountReal (H := (⊥ : SimpleGraph V_H)) G =
        (Nat.card V_G : ℝ) ^ (Nat.card V_H) := by
  intro V_H V_G instH instG G
  classical
  unfold homCountReal
  -- Build an equivalence between homomorphisms from ⊥ and functions
  let e : ((⊥ : SimpleGraph V_H) →g G) ≃ (V_H → V_G) :=
    { toFun := fun f => f
      invFun := fun g =>
        ⟨g, by
          intro a b hab
          cases hab⟩
      left_inv := by
        intro f
        ext a
        rfl
      right_inv := by
        intro g
        rfl }
  have hc : Nat.card ((⊥ : SimpleGraph V_H) →g G) = Nat.card (V_H → V_G) :=
    Nat.card_congr e
  -- Rewrite via the equivalence and compute the remaining cardinality
  rw [hc]
  -- `Nat.card_fun` computes the cardinality of the function type
  simpa [Nat.card_fun]
