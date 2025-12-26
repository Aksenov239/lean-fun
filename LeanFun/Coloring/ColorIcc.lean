import Mathlib

namespace LeanFun

/-- The subtype of natural numbers between `1` and `N` (inclusive). -/
def ColorIcc (N : ℕ) : Type := {n : ℕ // n ∈ Set.Icc (1 : ℕ) N}

/-- Convert a `Fin N` element to the corresponding element of `ColorIcc N` by adding 1. -/
def finToColorIcc (N : ℕ) : Fin N → ColorIcc N := fun i =>
  ⟨i.1 + 1, by
    have hi : i.1 < N := i.2
    exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt hi⟩⟩

end LeanFun
