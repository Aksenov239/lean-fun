import Mathlib
import LeanFun.Coloring.auxGraphC3_adj_of_adj
import LeanFun.Coloring.auxGraphC3_neighbor_image_card_ge_min3
import LeanFun.Coloring.C3Medium.auxGraphC3_colorable_medium

namespace LeanFun.Coloring

theorem exists_coloring_c3_medium_fin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * c - 1
    ∃ g : V → Fin N,
      (∀ ⦃u v : V⦄, G.Adj u v → g u ≠ g v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        let s := G.neighborFinset v
        (s.image g).card ≥ k) := by
  classical
  simp (config := { zeta := true })
  have hc : (LeanFun.Coloring.auxGraphC3 G).Colorable (D * 3 - 1) :=
    auxGraphC3_colorable_medium (G := G) (D := D) (hD := hD) (hdeg := hdeg)
  rcases hc with ⟨C⟩
  refine ⟨C, ?_, ?_⟩
  · intro u v huv
    have : (LeanFun.Coloring.auxGraphC3 G).Adj u v :=
      auxGraphC3_adj_of_adj (G := G) huv
    exact C.valid this
  · intro v
    simp (config := { zeta := true })
    have hN : D * 3 - 1 ≤ D * 3 := by
      exact Nat.sub_le (D * 3) 1
    let emb : Fin (D * 3 - 1) ↪ Fin (D * 3) := Fin.castLEEmb hN
    let f : V → Fin (D * 3) := fun x => emb (C x)
    have hfproper :
        ∀ ⦃u v : V⦄, (LeanFun.Coloring.auxGraphC3 G).Adj u v → f u ≠ f v := by
      intro u v huv hEq
      apply (C.valid huv)
      exact emb.injective hEq
    have hneigh_f :
        ((G.neighborFinset v).image f).card ≥ min 3 (G.degree v) := by
      have hAll :=
        auxGraphC3_neighbor_image_card_ge_min3 (G := G) (D := D) (hdeg := hdeg)
      simpa [f] using (hAll f hfproper v)
    have himage :
        ((G.neighborFinset v).image C).image emb =
          (G.neighborFinset v).image f := by
      simpa [f, Function.comp] using
        (Finset.image_image (s := G.neighborFinset v) (f := C) (g := emb))
    have hcard :
        ((G.neighborFinset v).image f).card =
          ((G.neighborFinset v).image C).card := by
      calc
        ((G.neighborFinset v).image f).card =
            (((G.neighborFinset v).image C).image emb).card := by
          simpa [himage]
        _ = ((G.neighborFinset v).image C).card := by
          simpa using
            (Finset.card_image_of_injective ((G.neighborFinset v).image C)
              emb.injective)
    simpa [hcard] using hneigh_f

end LeanFun.Coloring

