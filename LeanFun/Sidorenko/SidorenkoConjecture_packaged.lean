import Mathlib
import LeanFun.Sidorenko.Defs
import LeanFun.Sidorenko.sidorenko_edgeless_H
import LeanFun.Sidorenko.sidorenko_trivial_of_G_edgeless

open scoped BigOperators

theorem SidorenkoConjecture_packaged :
    ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
      (H : SimpleGraph V_H) (G : SimpleGraph V_G),
      (H.IsBipartite → H.edgeSet ≠ ∅ → G.edgeSet ≠ ∅ →
        ((Nat.card (H →g G) : ℝ) ≥ sidorenkoRHS H G)) →
      H.IsBipartite →
        ((Nat.card (H →g G) : ℝ) ≥ sidorenkoRHS H G) := by
  classical
  intro V_H V_G instVH instVG H G hNontriv hBip
  by_cases hH0 : H.edgeSet = ∅
  · exact sidorenko_edgeless_H (H := H) (G := G) hH0
  · by_cases hG0 : G.edgeSet = ∅
    · exact sidorenko_trivial_of_G_edgeless (H := H) (G := G) hH0 hG0
    · exact hNontriv hBip hH0 hG0

