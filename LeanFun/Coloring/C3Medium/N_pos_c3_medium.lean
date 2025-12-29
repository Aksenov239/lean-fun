import Mathlib
import LeanFun.Coloring.C3Medium.eight_le_D_of_pow_three_le

namespace LeanFun.Coloring

theorem N_pos_c3_medium (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D) : 0 < D * 3 - 1 := by
  have h8 : 8 ≤ D := eight_le_D_of_pow_three_le D hD
  have h24 : 24 ≤ D * 3 := by
    simpa using (Nat.mul_le_mul_right 3 h8)
  have h1lt24 : 1 < 24 := by decide
  have h1lt : 1 < D * 3 := lt_of_lt_of_le h1lt24 h24
  exact Nat.sub_pos_of_lt h1lt

end LeanFun.Coloring

