import Mathlib

namespace LeanFun.Coloring

theorem eight_le_D_of_pow_three_le (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D) : 8 ≤ D := by
  simpa using hD

end LeanFun.Coloring

