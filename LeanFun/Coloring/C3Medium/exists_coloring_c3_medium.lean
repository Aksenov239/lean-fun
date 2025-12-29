import Mathlib
import LeanFun.Coloring.C3Medium.colorOfFin_injective
import LeanFun.Coloring.C3Medium.card_image_colorOfFin_comp
import LeanFun.Coloring.C3Medium.exists_coloring_c3_medium_fin

namespace LeanFun.Coloring

theorem exists_coloring_c3_medium {V : Type*} [Fintype V] [DecidableEq V]
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
        let s := G.neighborFinset v
        (s.image (fun x => f x)).card ≥ k) := by
  classical
  simp (config := { zeta := true })
  rcases
      (by
          simpa using
            (exists_coloring_c3_medium_fin (V := V) (G := G) (D := D) hD hdeg)) with
    ⟨g, hgProper, hgCard⟩
  refine ⟨fun v => colorOfFin (D * 3 - 1) (g v), ?_, ?_⟩
  · intro u v huv
    intro hEq
    have : g u = g v := (colorOfFin_injective (D * 3 - 1)) hEq
    exact hgProper huv this
  · intro v
    let s := G.neighborFinset v
    have hcard :
        (s.image (fun x => colorOfFin (D * 3 - 1) (g x))).card =
          (s.image g).card :=
      Finset.card_image_colorOfFin_comp (D * 3 - 1) s g
    have hg' :
        3 ≤ (s.image g).card ∨ G.degree v ≤ (s.image g).card := by
      simpa [s] using (hgCard v)
    simpa [s, hcard] using hg'

end LeanFun.Coloring

