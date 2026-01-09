import Mathlib

theorem exists_root_sum_cos
    (s : Finset ℤ) (hs0 : s.card ≥ 2) :
    ∃ x : ℝ, (∑ n ∈ s, Real.cos ((n : ℝ) * x)) = 0 :=
  sorry
