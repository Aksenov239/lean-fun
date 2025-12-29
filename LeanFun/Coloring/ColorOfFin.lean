import LeanFun.Coloring.Base

namespace LeanFun.Coloring

abbrev ColorIccAbbrev (N : ℕ) : Type :=
  ColorIcc N

@[simp] theorem ColorIcc_abbrev (N : ℕ) : ColorIccAbbrev N = ColorIcc N :=
  rfl

noncomputable def colorOfFin (N : ℕ) (a : Fin N) : ColorIcc N :=
  finToColorIcc N a

lemma colorOfFin_def (N : ℕ) (a : Fin N) :
    colorOfFin N a =
      ⟨a.1 + 1,
        by
          refine Set.mem_Icc.mpr ?_
          constructor
          · exact Nat.succ_le_succ (Nat.zero_le _)
          · exact Nat.succ_le_of_lt a.2⟩ :=
  rfl

end LeanFun.Coloring
