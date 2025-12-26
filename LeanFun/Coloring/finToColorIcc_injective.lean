import LeanFun.Coloring.Base

namespace LeanFun.Coloring

theorem finToColorIcc_injective (N : ℕ) :
    Function.Injective (finToColorIcc N) := by
  intro a b h
  have hval : a.1 + 1 = b.1 + 1 := by
    simpa [finToColorIcc] using congrArg Subtype.val h
  have hab : a.1 = b.1 := by
    exact Nat.add_right_cancel hval
  exact Fin.ext hab

end LeanFun.Coloring

