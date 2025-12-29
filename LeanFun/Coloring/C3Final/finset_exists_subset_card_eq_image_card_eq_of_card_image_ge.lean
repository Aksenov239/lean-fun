import Mathlib

theorem Finset.exists_subset_card_eq_image_card_eq_of_card_image_ge
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (k : ℕ) :
    k ≤ (s.image f).card →
      ∃ t : Finset α, t ⊆ s ∧ t.card = k ∧ (t.image f).card = k := by
  intro hk
  classical
  -- choose `u ⊆ s.image f` with card k
  rcases Finset.exists_subset_card_eq hk with ⟨u, hu_sub, hu_card⟩
  -- for each y ∈ u, choose x ∈ s with f x = y
  have hx : ∀ y : {y // y ∈ u}, ∃ x : α, x ∈ s ∧ f x = y.1 := by
    intro y
    have hy' : y.1 ∈ s.image f := hu_sub y.2
    rcases (Finset.mem_image.mp hy') with ⟨x, hxS, hxEq⟩
    exact ⟨x, hxS, hxEq⟩
  choose g hg using hx
  let t : Finset α := u.attach.image g
  refine ⟨t, ?_, ?_, ?_⟩
  · intro x hx
    rcases (Finset.mem_image.mp hx) with ⟨y, hyu, rfl⟩
    exact (hg y).1
  · -- card t = k
    have hg_inj : Function.Injective g := by
      intro y1 y2 h
      apply Subtype.ext
      have : f (g y1) = f (g y2) := congrArg f h
      simpa [hg y1, hg y2] using this
    have ht_card' : t.card = u.attach.card := by
      simpa [t] using (Finset.card_image_of_injective (s := u.attach) (f := g) hg_inj)
    have ht_card : t.card = u.card := by
      calc
        t.card = u.attach.card := ht_card'
        _ = u.card := by simpa using (Finset.card_attach u)
    simpa [ht_card, hu_card]
  · -- (t.image f).card = k
    have htu : t.image f = u := by
      ext y
      constructor
      · intro hy
        rcases (Finset.mem_image.mp hy) with ⟨x, hxT, hxEq⟩
        rcases (Finset.mem_image.mp hxT) with ⟨y0, hy0, rfl⟩
        have hf0 : f (g y0) = y0.1 := (hg y0).2
        have : y = y0.1 := by
          -- simp using hxEq : f (g y0) = y
          simpa [hxEq] using hf0
        simpa [this] using y0.2
      · intro hyu
        have hy_attach : (⟨y, hyu⟩ : {y // y ∈ u}) ∈ u.attach := by
          simpa using hyu
        refine Finset.mem_image.mpr ?_
        refine ⟨g ⟨y, hyu⟩, ?_, ?_⟩
        · -- g y ∈ t
          refine Finset.mem_image.mpr ?_
          refine ⟨⟨y, hyu⟩, hy_attach, rfl⟩
        · -- f (g y) = y
          simpa using (hg ⟨y, hyu⟩).2
    simpa [htu, hu_card]
