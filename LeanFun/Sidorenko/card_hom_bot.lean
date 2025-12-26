import Mathlib

open scoped BigOperators

theorem card_hom_bot :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G] (G : SimpleGraph V_G),
      Nat.card ((⊥ : SimpleGraph V_H) →g G) = Nat.card V_G ^ Nat.card V_H := by
  classical
  intro V_H V_G _ _ G
  -- Explicit equivalence between graph homs from ⊥ and functions
  let e : ((⊥ : SimpleGraph V_H) →g G) ≃ (V_H → V_G) :=
    { toFun := fun f => f
      invFun := fun g =>
        ⟨g, by
          intro a b h
          cases h⟩
      left_inv := by
        intro f
        ext a
        rfl
      right_inv := by
        intro g
        rfl }
  -- Compute the cardinality via the equivalence
  simpa using (Nat.card_congr e).trans (Nat.card_fun (α := V_H) (β := V_G))
