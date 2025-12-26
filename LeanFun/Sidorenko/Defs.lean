import Mathlib

open scoped BigOperators

noncomputable def edgeDensityK2 {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  (2 * (Nat.card (↑G.edgeSet) : ℝ)) / ((Nat.card V : ℝ) ^ (2 : ℕ))

noncomputable def sidorenkoRHS {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
    (H : SimpleGraph V_H) (G : SimpleGraph V_G) : ℝ :=
  (edgeDensityK2 G) ^ (Nat.card (↑H.edgeSet)) * ((Nat.card V_G : ℝ) ^ Nat.card V_H)
