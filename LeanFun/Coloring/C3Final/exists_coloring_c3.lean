import LeanFun.Coloring.C3Final.exists_coloring_fin_c3
import LeanFun.Coloring.C3Final.finset_exists_subset_card_eq_image_card_eq_of_card_image_ge
import LeanFun.Coloring.card_image_finToColorIcc
import LeanFun.Coloring.finToColorIcc_injective

namespace LeanFun.Coloring

theorem exists_coloring_c3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * c - 1
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        ∃ s : Finset V,
          s ⊆ G.neighborFinset v ∧
          s.card = k ∧
          (s.image (fun x => f x)).card = k) := by
  classical
  simp (config := { zeta := true })
  rcases (by
      simpa (config := { zeta := true })
        using (exists_coloring_fin_c3 (G := G) (D := D) hD hdeg)) with
    ⟨g, hgProper, hgNeigh⟩
  -- set N to match the one used for `g`
  let N : ℕ := D * 3 - 1
  -- rewrite `g`'s codomain to `Fin N`
  have hN : D * 3 - 1 = N := by rfl
  -- transport g along definitional equality
  -- define f via finToColorIcc
  --
  -- (We could avoid the casts by simply using `N := D * 3 - 1` everywhere,
  --  but naming it makes later steps cleaner.)
  refine
    ⟨fun v => LeanFun.Coloring.finToColorIcc (N := D * 3 - 1) (g v), ?_, ?_⟩
  · intro u v huv
    intro hEq
    exact (hgProper huv) (LeanFun.Coloring.finToColorIcc_injective (N := D * 3 - 1) hEq)
  · intro v
    let k : ℕ := min 3 (G.degree v)
    have hk : k ≤ ((G.neighborFinset v).image g).card := by
      simpa [k] using (hgNeigh v)
    rcases
        (Finset.exists_subset_card_eq_image_card_eq_of_card_image_ge
          (s := G.neighborFinset v) (f := g) (k := k) hk) with
      ⟨s, hsSub, hsCard, hsImg⟩
    refine ⟨s, hsSub, hsCard, ?_⟩
    have hcard : (s.image (fun x => LeanFun.Coloring.finToColorIcc (N := D * 3 - 1) (g x))).card =
        (s.image g).card := by
      simpa using
        (LeanFun.Coloring.card_image_finToColorIcc (N := D * 3 - 1) (s := s) (f := g))
    -- finish by rewriting with hcard
    calc
      (s.image (fun x => LeanFun.Coloring.finToColorIcc (N := D * 3 - 1) (g x))).card =
          (s.image g).card := hcard
      _ = k := hsImg

end LeanFun.Coloring
