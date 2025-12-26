import Mathlib
import LeanFun.Sidorenko.Definitions
import LeanFun.Sidorenko.SidorenkoConjectureSimplified

theorem SidorenkoConjecture :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      H.IsBipartite → Nat.card (↑H.edgeSet) = 0 →
        ((Nat.card (H →g G) : ℝ) ≥
          (((2 * (Nat.card (↑G.edgeSet) : ℝ)) /
                ((Nat.card V_G : ℝ) ^ (2 : Nat))) ^
              (Nat.card (↑H.edgeSet))) *
            ((Nat.card V_G : ℝ) ^ (Nat.card V_H))) := by
  classical
  intro V_H V_G _instH _instG H G hBip
  simpa [homCountReal, sidorenkoLowerBound, globalEdgeDensity] using
    (SidorenkoConjecture_simplified (H := H) (G := G) hBip)
