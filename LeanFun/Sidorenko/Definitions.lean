import Mathlib

noncomputable section

/-- The real-valued count of graph homomorphisms from `H` to `G`. -/
def homCountReal {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
    (H : SimpleGraph V_H) (G : SimpleGraph V_G) : ℝ :=
  (Nat.card (H →g G) : ℝ)

/-- The homomorphism density of `H` in `G`. -/
def homDensity {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
    (H : SimpleGraph V_H) (G : SimpleGraph V_G) : ℝ :=
  homCountReal H G / ((Nat.card V_G : ℝ) ^ (Nat.card V_H))

/-- The edge density of a graph `G`. -/
def globalEdgeDensity {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℝ :=
  (2 * (Nat.card (↑G.edgeSet) : ℝ)) / ((Nat.card V : ℝ) ^ (2 : Nat))

/-- The lower bound appearing in Sidorenko's conjecture. -/
def sidorenkoLowerBound {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
    (H : SimpleGraph V_H) (G : SimpleGraph V_G) : ℝ :=
  (globalEdgeDensity (V := V_G) G) ^ (Nat.card (↑H.edgeSet)) *
    ((Nat.card V_G : ℝ) ^ (Nat.card V_H))

end
