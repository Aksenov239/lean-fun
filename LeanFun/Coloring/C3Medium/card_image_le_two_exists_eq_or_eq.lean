import Mathlib

namespace LeanFun.Coloring

theorem Finset.card_image_le_two_exists_eq_or_eq {α β : Type*} [DecidableEq β]
    [Nonempty β] (s : Finset α) (g : α → β) :
    (s.image g).card ≤ 2 →
      ∃ a b : β, ∀ x ∈ s, g x = a ∨ g x = b := by
  intro hcard
  classical
  have hlt_or_eq : (s.image g).card < 2 ∨ (s.image g).card = 2 :=
    Nat.lt_or_eq_of_le hcard
  cases hlt_or_eq with
  | inl hlt2 =>
      have hle1 : (s.image g).card ≤ 1 := Nat.lt_succ_iff.mp hlt2
      have hlt1_or_eq1 :
          (s.image g).card < 1 ∨ (s.image g).card = 1 :=
        Nat.lt_or_eq_of_le hle1
      cases hlt1_or_eq1 with
      | inl hlt1 =>
          have hle0 : (s.image g).card ≤ 0 := Nat.lt_succ_iff.mp hlt1
          have hcard0 : (s.image g).card = 0 := Nat.eq_zero_of_le_zero hle0
          have himg_empty : s.image g = ∅ :=
            Finset.card_eq_zero.mp hcard0
          have hs_empty : s = ∅ :=
            (Finset.image_eq_empty.mp himg_empty)
          obtain ⟨b0⟩ := ‹Nonempty β›
          refine ⟨b0, b0, ?_⟩
          simp [hs_empty]
      | inr hcard1 =>
          rcases (Finset.card_eq_one.mp hcard1) with ⟨a, ha⟩
          refine ⟨a, a, ?_⟩
          intro x hx
          have hximg : g x ∈ s.image g :=
            Finset.mem_image_of_mem g hx
          have hx' : g x ∈ ({a} : Finset β) := by
            simpa [ha] using hximg
          have hxa : g x = a := by
            simpa using hx'
          exact Or.inl hxa
  | inr hcard2 =>
      rcases (Finset.card_eq_two.mp hcard2) with
        ⟨a, b, hab, habs⟩
      refine ⟨a, b, ?_⟩
      intro x hx
      have hximg : g x ∈ s.image g :=
        Finset.mem_image_of_mem g hx
      have hx' : g x ∈ ({a, b} : Finset β) := by
        simpa [habs] using hximg
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx'

end LeanFun.Coloring

