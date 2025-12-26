import Mathlib

namespace LeanFun.Coloring

theorem SimpleGraph_colorable_of_forall_finset_exists_degree_lt {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, ((G.neighborFinset v ∩ s).card < n)) :
    G.Colorable n := by
  classical
  cases n with
  | zero =>
      have hV : IsEmpty V := by
        classical
        by_contra hne
        haveI : Nonempty V := not_isEmpty_iff.mp hne
        have huniv : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
        rcases h (Finset.univ : Finset V) huniv with ⟨v, hv, hvlt⟩
        exact (Nat.not_lt_zero _ hvlt)
      haveI : IsEmpty V := hV
      simpa using (G.colorable_of_isEmpty 0)
  | succ n =>
      classical
      let P : Finset V → Prop := fun s =>
        ∃ f : V → Fin (Nat.succ n),
          ∀ ⦃u v⦄, u ∈ s → v ∈ s → G.Adj u v → f u ≠ f v

      have hUniv : P (Finset.univ : Finset V) := by
        classical
        refine (Finset.univ : Finset V).strongInductionOn ?_
        intro s ih
        by_cases hs : s.Nonempty
        · rcases h s hs with ⟨v, hv, hvdeg⟩
          have hs' : s.erase v ⊂ s := Finset.erase_ssubset hv
          rcases ih (s.erase v) hs' with ⟨f, hf⟩

          let N : Finset V := G.neighborFinset v ∩ s.erase v
          let forbidden : Finset (Fin (Nat.succ n)) := N.image f

          have hforbidden_lt : forbidden.card < Nat.succ n := by
            have hle₁ : forbidden.card ≤ N.card := by
              simpa [forbidden] using (Finset.card_image_le (s := N) (f := f))
            have hNle : N.card ≤ (G.neighborFinset v ∩ s).card := by
              have hNsub : N ⊆ G.neighborFinset v ∩ s := by
                intro w hw
                rcases Finset.mem_inter.mp hw with ⟨hwN, hwsv⟩
                have hws : w ∈ s := Finset.mem_of_mem_erase hwsv
                exact Finset.mem_inter.mpr ⟨hwN, hws⟩
              exact Finset.card_le_card hNsub
            exact lt_of_le_of_lt (le_trans hle₁ hNle) hvdeg

          have hcard_lt : forbidden.card < (Finset.univ : Finset (Fin (Nat.succ n))).card := by
            simpa using hforbidden_lt
          rcases Finset.exists_mem_not_mem_of_card_lt_card hcard_lt with ⟨c, hcuniv, hcnot⟩

          refine ⟨fun x => if hx : x = v then c else f x, ?_⟩
          intro u w hu hw huw

          by_cases huv : u = v
          · -- u = v
            subst u
            have hwv : w ≠ v := by
              intro hEq
              subst w
              exact G.loopless v huw
            have hw' : w ∈ s.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
            have hwN : w ∈ N := by
              have : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).2 huw
              exact Finset.mem_inter.mpr ⟨this, hw'⟩
            have hfw_mem : f w ∈ forbidden := Finset.mem_image_of_mem f hwN
            have hne : c ≠ f w := by
              intro hEq
              have : c ∈ forbidden := by simpa [hEq] using hfw_mem
              exact hcnot this
            simpa [hwv] using hne

          · by_cases hwv : w = v
            · -- w = v
              subst w
              have hu' : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
              have huN : u ∈ N := by
                have : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).2 (G.symm huw)
                exact Finset.mem_inter.mpr ⟨this, hu'⟩
              have hfu_mem : f u ∈ forbidden := Finset.mem_image_of_mem f huN
              have hne : f u ≠ c := by
                intro hEq
                have : c ∈ forbidden := by simpa [hEq] using hfu_mem
                exact hcnot this
              simpa [huv] using hne

            · -- neither endpoint is v
              have hu' : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
              have hw' : w ∈ s.erase v := Finset.mem_erase.mpr ⟨hwv, hw⟩
              have : f u ≠ f w := hf hu' hw' huw
              simpa [huv, hwv] using this

        · -- s = ∅
          have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
          subst hs0
          refine ⟨fun _ => 0, ?_⟩
          intro u v hu
          simp at hu

      rcases hUniv with ⟨f, hf⟩
      refine ⟨SimpleGraph.Coloring.mk (G := G) f ?_⟩
      intro u v huv
      exact hf (Finset.mem_univ u) (Finset.mem_univ v) huv

end LeanFun.Coloring

