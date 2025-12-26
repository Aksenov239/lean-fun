import Mathlib
import LeanFun.Sidorenko.Defs
import LeanFun.Sidorenko.SidorenkoConjecture_packaged

open scoped BigOperators

theorem SidorenkoConjecture :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      (H.IsBipartite → H.edgeSet ≠ ∅ → G.edgeSet ≠ ∅ →
        ((Nat.card (H →g G) : ℝ) ≥ sidorenkoRHS H G)) →
      H.IsBipartite →
        ((Nat.card (H →g G) : ℝ) ≥
          (((2 * (Nat.card (↑G.edgeSet) : ℝ))
              / ((Nat.card V_G : ℝ) ^ (2 : Nat))) ^ (Nat.card (↑H.edgeSet))) *
            ((Nat.card V_G : ℝ) ^ (Nat.card V_H))) := by
  classical
  intro V_H V_G _ _ H G hNontriv hBip
  have h : (Nat.card (H →g G) : ℝ) ≥ sidorenkoRHS H G :=
    SidorenkoConjecture_packaged (H := H) (G := G) hNontriv hBip
  simpa [sidorenkoRHS, edgeDensityK2] using h

