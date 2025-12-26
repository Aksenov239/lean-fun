import Mathlib

namespace LeanFun.Coloring

noncomputable def ColorIcc (N : ℕ) :=
  {n : ℕ // n ∈ Set.Icc (1 : ℕ) N}

instance instDecidableEqColorIcc (N : ℕ) : DecidableEq (ColorIcc N) := by
  dsimp [ColorIcc]
  infer_instance

noncomputable def finToColorIcc (N : ℕ) (a : Fin N) : ColorIcc N :=
  ⟨a.1 + 1,
    by
      refine Set.mem_Icc.mpr ?_
      constructor
      · exact Nat.succ_le_succ (Nat.zero_le _)
      · exact Nat.succ_le_of_lt a.2⟩

noncomputable def Tmin3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Classical.choose
    (Finset.exists_subset_card_eq (s := G.neighborFinset v)
      (n := min 3 (G.degree v))
      (by
        have hcard : (G.neighborFinset v).card = G.degree v := by
          simpa using (SimpleGraph.card_neighborFinset_eq_degree (G := G) v)
        simpa [hcard] using (Nat.min_le_right 3 (G.degree v))))

def auxGraphC3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V where
  Adj u v :=
    G.Adj u v ∨ ∃ w, u ∈ Tmin3 (G := G) w ∧ v ∈ Tmin3 (G := G) w ∧ u ≠ v
  symm := by
    intro u v h
    rcases h with h | ⟨w, huw, hwv, hne⟩
    · exact Or.inl (G.symm h)
    · refine Or.inr ⟨w, hwv, huw, ?_⟩
      simpa using hne.symm
  loopless := by
    intro v
    intro h
    rcases h with h | ⟨w, hvw, hww, hne⟩
    · exact (G.loopless v) h
    · exact hne (by rfl)

end LeanFun.Coloring
