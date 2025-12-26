import LeanFun.Coloring.finToColorIcc_injective

namespace LeanFun.Coloring

theorem card_image_finToColorIcc {α : Type*} [DecidableEq α] (N : ℕ) (s : Finset α)
    (f : α → Fin N) :
    (s.image (fun x => finToColorIcc N (f x))).card = (s.image f).card := by
  classical
  simpa [Finset.image_image] using
    (Finset.card_image_of_injective (s := s.image f) (f := finToColorIcc N)
      (finToColorIcc_injective N))

end LeanFun.Coloring

