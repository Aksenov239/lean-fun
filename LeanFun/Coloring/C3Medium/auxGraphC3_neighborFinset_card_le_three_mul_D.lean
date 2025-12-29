import Mathlib
import LeanFun.Coloring.auxGraphC3_degree_le_three_mul_degree

namespace LeanFun.Coloring

theorem auxGraphC3_neighborFinset_card_le_three_mul_D {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdeg : ∀ v : V, G.degree v ≤ D)
    [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj]
    (v : V) :
    ((LeanFun.Coloring.auxGraphC3 G).neighborFinset v).card ≤ D * 3 := by
  classical
  let H : SimpleGraph V := LeanFun.Coloring.auxGraphC3 G
  have h1 : H.degree v ≤ 3 * G.degree v := by
    simpa [H] using
      (LeanFun.Coloring.auxGraphC3_degree_le_three_mul_degree (G := G) v)
  have h2 : 3 * G.degree v ≤ 3 * D := by
    exact Nat.mul_le_mul_left 3 (hdeg v)
  have hdeg' : H.degree v ≤ 3 * D := le_trans h1 h2
  have hcard : (H.neighborFinset v).card ≤ 3 * D := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree (G := H) v] using hdeg'
  simpa [H, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

end LeanFun.Coloring

