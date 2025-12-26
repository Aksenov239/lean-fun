import Mathlib
import LeanFun.Coloring.ColorIcc

namespace LeanFun

theorem finToColorIcc_injective (N : ℕ) :
    Function.Injective (finToColorIcc N) := by
  intro i j hij
  apply Fin.ext
  have hval : i.1 + 1 = j.1 + 1 := by
    simpa [finToColorIcc] using congrArg Subtype.val hij
  have hs : Nat.succ i.1 = Nat.succ j.1 := by
    simpa [Nat.succ_eq_add_one] using hval
  exact Nat.succ_injective hs

end LeanFun
