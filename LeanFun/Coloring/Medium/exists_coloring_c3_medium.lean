import LeanFun.Coloring.Medium.exists_coloring_fin_c3_medium
import LeanFun.Coloring.card_image_finToColorIcc
import LeanFun.Coloring.finToColorIcc_injective

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
        (s.image (fun x => f x)).card >= k) := by
  classical
  dsimp
  have h :=
    exists_coloring_fin_c3_medium (V := V) (G := G) (D := D) hD hdeg
  dsimp at h
  rcases h with ⟨g, hgproper, hgcard⟩
  refine
    ⟨fun v => LeanFun.Coloring.finToColorIcc (D * 3 - 1) (g v), ?_, ?_⟩
  · intro u v huv hEq
    have hguv : g u = g v :=
      (LeanFun.Coloring.finToColorIcc_injective (N := D * 3 - 1)) hEq
    exact (hgproper huv) hguv
  · intro v
    dsimp
    have hgcardv := hgcard v
    simpa [
      LeanFun.Coloring.card_image_finToColorIcc (N := D * 3 - 1)
        (s := G.neighborFinset v) (f := g)
    ] using hgcardv

end LeanFun.Coloring

