import Mathlib

namespace LeanFun

open scoped Classical

variable {V : Type*}

-- The proofs provided are already correct; we include them verbatim.

theorem exists_proper_coloring_of_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (m : ℕ)
    (hdeg : ∀ v : V, H.degree v ≤ m) :
    ∃ f : V → Fin (m + 1), ∀ ⦃u v : V⦄, H.Adj u v → f u ≠ f v := by
  classical
  -- We prove the statement by induction on the number of vertices.
  have hP :
      (∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v : V, G.degree v ≤ m) →
          ∃ f : V → Fin (m + 1), ∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) := by
    classical
    refine
      (Fintype.induction_subsingleton_or_nontrivial (α := V)
        (P := fun α _ =>
          ∀ (G : SimpleGraph α) [DecidableRel G.Adj],
            (∀ v : α, G.degree v ≤ m) →
              ∃ f : α → Fin (m + 1), ∀ ⦃u v : α⦄, G.Adj u v → f u ≠ f v)
        ?_ ?_ )
    · -- Subsingleton case.
      intro α _
      intro _instSub
      intro G _ hdegG
      refine ⟨fun _ => (0 : Fin (m + 1)), ?_⟩
      intro u v huv
      have hUV : u = v := Subsingleton.elim u v
      subst hUV
      exact (G.loopless _ huv).elim
    · -- Inductive step.
      intro α _
      intro _instNontr ih
      intro G _ hdegG
      classical
      let x : α := Classical.choice (by infer_instance : Nonempty α)
      let s : Set α := {v | v ≠ x}
      have hs_card : Fintype.card s < Fintype.card α := by
        simpa [s] using
          (Fintype.card_subtype_lt (α := α) (p := fun v : α => v ≠ x) (x := x) (by simp))
      have hs :
          ∀ (G' : SimpleGraph s) [DecidableRel G'.Adj],
            (∀ v : s, G'.degree v ≤ m) →
              ∃ f : s → Fin (m + 1), ∀ ⦃u v : s⦄, G'.Adj u v → f u ≠ f v :=
        ih s hs_card
      have hdeg_induce : ∀ v : s, (G.induce s).degree v ≤ m := by
        intro v
        have hmap := (G.map_neighborFinset_induce (s := s) (v := v))
        have hcardmap := congrArg Finset.card hmap
        have hcard : ((G.induce s).neighborFinset v).card = (G.neighborFinset v.1 ∩ s.toFinset).card := by
          simpa using hcardmap
        have hinter : (G.neighborFinset v.1 ∩ s.toFinset).card ≤ (G.neighborFinset v.1).card := by
          -- intersection is a subset of the left set
          exact Finset.card_le_card (Finset.inter_subset_left)
        have hcard_le : ((G.induce s).neighborFinset v).card ≤ (G.neighborFinset v.1).card := by
          simpa [hcard] using hinter
        have hdeg_le : (G.induce s).degree v ≤ G.degree v.1 := by
          have hdeg1 : ((G.induce s).neighborFinset v).card = (G.induce s).degree v := by
            simpa using
              (SimpleGraph.card_neighborFinset_eq_degree (G := (G.induce s)) (v := v))
          have hdeg2 : (G.neighborFinset v.1).card = G.degree v.1 := by
            simpa using
              (SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v.1))
          -- rewrite degrees as cardinals
          rw [← hdeg1, ← hdeg2]
          exact hcard_le
        exact le_trans hdeg_le (hdegG v.1)
      obtain ⟨g, hg⟩ := hs (G.induce s) hdeg_induce
      -- Auxiliary coloring on all of `α` (using `0` on `x`).
      let g' : α → Fin (m + 1) := fun v =>
        if hv : v = x then (0 : Fin (m + 1)) else g ⟨v, by simpa [s] using hv⟩
      let S : Finset (Fin (m + 1)) := (G.neighborFinset x).image g'
      have hS_card_le : S.card ≤ m := by
        have h1 : S.card ≤ (G.neighborFinset x).card := by
          simpa [S] using (Finset.card_image_le (s := G.neighborFinset x) (f := g'))
        have h2 : (G.neighborFinset x).card = G.degree x := by
          simpa using (SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := x))
        have h3 : (G.neighborFinset x).card ≤ m := by
          simpa [h2] using hdegG x
        exact le_trans h1 h3
      have hS_lt : S.card < (Finset.univ : Finset (Fin (m + 1))).card := by
        simpa using (Nat.lt_succ_of_le hS_card_le : S.card < m + 1)
      obtain ⟨c, -, hcS⟩ := Finset.exists_mem_notMem_of_card_lt_card hS_lt
      -- Extend the coloring, setting `f x = c`.
      refine ⟨fun v => if hv : v = x then c else g ⟨v, by simpa [s] using hv⟩, ?_⟩
      intro u v huv
      classical
      by_cases hu : u = x
      · subst hu
        by_cases hv : v = x
        · subst hv
          exact (G.loopless _ huv).elim
        · have hv' : v ∈ G.neighborFinset x := by
            simpa [SimpleGraph.mem_neighborFinset] using (show G.Adj x v from huv)
          have hmem_g' : g' v ∈ S := by
            refine Finset.mem_image.mpr ?_
            exact ⟨v, hv', rfl⟩
          have hgv : g' v = g ⟨v, by simpa [s] using hv⟩ := by
            simp [g', hv]
          have hmem : g ⟨v, by simpa [s] using hv⟩ ∈ S := by
            simpa [hgv] using hmem_g'
          -- simplify the goal to `c ≠ g ...`
          simp [hv]
          intro hEq
          apply hcS
          simpa [hEq] using hmem
      · by_cases hv : v = x
        · subst hv
          have hu' : u ∈ G.neighborFinset x := by
            have : G.Adj x u := G.adj_symm huv
            simpa [SimpleGraph.mem_neighborFinset] using this
          have hmem_g' : g' u ∈ S := by
            refine Finset.mem_image.mpr ?_
            exact ⟨u, hu', rfl⟩
          have hgu : g' u = g ⟨u, by simpa [s] using hu⟩ := by
            simp [g', hu]
          have hmem : g ⟨u, by simpa [s] using hu⟩ ∈ S := by
            simpa [hgu] using hmem_g'
          -- simplify the goal to `g ... ≠ c`
          simp [hu]
          intro hEq
          apply hcS
          -- `hEq : g ... = c`
          simpa [hEq] using hmem
        · have huS : u ∈ s := by simpa [s] using hu
          have hvS : v ∈ s := by simpa [s] using hv
          have hadj' : (G.induce s).Adj ⟨u, huS⟩ ⟨v, hvS⟩ := by
            simpa [SimpleGraph.induce] using huv
          simpa [hu, hv, s] using (hg hadj')
  exact hP H hdeg

end LeanFun
