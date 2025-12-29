import LeanFun.Coloring.ColorOfFin

namespace LeanFun.Coloring

theorem colorOfFin_injective (N : ℕ) :
    Function.Injective (colorOfFin N) := by
  intro i j h
  apply Fin.ext
  have h' : i.1 + 1 = j.1 + 1 := by
    exact congrArg Subtype.val h
  exact Nat.add_right_cancel h'

end LeanFun.Coloring

