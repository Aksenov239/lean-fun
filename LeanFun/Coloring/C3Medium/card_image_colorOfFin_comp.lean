import Mathlib
import LeanFun.Coloring.C3Medium.colorOfFin_injective

namespace LeanFun.Coloring

theorem Finset.card_image_colorOfFin_comp {α : Type*} [DecidableEq α]
    (N : ℕ) (s : Finset α) (g : α → Fin N) :
    (s.image (fun x => colorOfFin N (g x))).card = (s.image g).card := by
  classical
  have himage :
      (s.image g).image (colorOfFin N) = s.image (fun x => colorOfFin N (g x)) := by
    simpa [Function.comp] using
      (Finset.image_image (s := s) (f := g) (g := colorOfFin N))
  rw [← himage]
  simpa using
    (Finset.card_image_of_injective (s := s.image g) (f := colorOfFin N)
      (colorOfFin_injective N))

end LeanFun.Coloring

