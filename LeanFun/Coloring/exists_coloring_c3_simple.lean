import LeanFun.Coloring.card_image_finToColorIcc
import LeanFun.Coloring.exists_coloring_fin_c3_simple

namespace LeanFun.Coloring

theorem exists_coloring_c3_simple {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * c
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        let s := G.neighborFinset v
        (s.image (fun x => f x)).card >= k) := by
  classical
  dsimp
  have hfin := exists_coloring_fin_c3_simple (G := G) (D := D) hD hdeg
  dsimp at hfin
  rcases hfin with ⟨g, hgproper, hgcard⟩
  refine ⟨fun v => finToColorIcc (D * 3) (g v), ?_, ?_⟩
  · intro u v huv
    have hguv : g u ≠ g v := hgproper huv
    intro hEq
    apply hguv
    exact finToColorIcc_injective (D * 3) (by simpa using hEq)
  · intro v
    have hgcard' : ((G.neighborFinset v).image g).card ≥ min 3 (G.degree v) := by
      simpa using (hgcard v)
    have hcardEq :
        ((G.neighborFinset v).image (fun x => finToColorIcc (D * 3) (g x))).card =
          ((G.neighborFinset v).image g).card := by
      simpa using
        (card_image_finToColorIcc (α := V) (N := (D * 3)) (s := G.neighborFinset v) (f := g))
    calc
      ((G.neighborFinset v).image (fun x => finToColorIcc (D * 3) (g x))).card =
          ((G.neighborFinset v).image g).card := hcardEq
      _ ≥ min 3 (G.degree v) := hgcard'

end LeanFun.Coloring

