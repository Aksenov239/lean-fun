import LeanFun.Coloring.Medium.auxGraphC3_colorable_medium
import LeanFun.Coloring.auxGraphC3_adj_of_adj
import LeanFun.Coloring.auxGraphC3_neighbor_image_card_ge_min3

namespace LeanFun.Coloring

theorem exists_coloring_fin_c3_medium {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * c - 1
    ∃ f : V → Fin N,
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        let s := G.neighborFinset v
        (s.image (fun x => f x)).card >= k) := by
  classical
  dsimp
  have hc : (LeanFun.Coloring.auxGraphC3 G).Colorable (D * 3 - 1) :=
    auxGraphC3_colorable_medium (G := G) (D := D) (hD := hD) (hdeg := hdeg)
  let C : (LeanFun.Coloring.auxGraphC3 G).Coloring (Fin (D * 3 - 1)) := hc.some
  let f : V → Fin (D * 3 - 1) := fun v => C v
  have hproper_aux :
      ∀ ⦃u v : V⦄, (LeanFun.Coloring.auxGraphC3 G).Adj u v → f u ≠ f v := by
    intro u v huv
    simpa [f] using (C.valid huv)

  have hN : D * 3 - 1 ≤ D * 3 := by
    exact Nat.sub_le (D * 3) 1
  let f' : V → Fin (D * 3) := fun v => (f v).castLE hN
  have hproper_aux' :
      ∀ ⦃u v : V⦄, (LeanFun.Coloring.auxGraphC3 G).Adj u v → f' u ≠ f' v := by
    intro u v huv hEq
    have hinj : Function.Injective (fun i : Fin (D * 3 - 1) => i.castLE hN) :=
      Fin.castLE_injective hN
    apply hproper_aux huv
    exact hinj hEq

  have hneigh' :
      ∀ v : V,
        ((G.neighborFinset v).image (fun x => f' x)).card ≥ min 3 (G.degree v) := by
    simpa [f'] using
      (LeanFun.Coloring.auxGraphC3_neighbor_image_card_ge_min3 (G := G) (D := D) hdeg f'
        hproper_aux')

  have hcardEq :
      ∀ v : V,
        ((G.neighborFinset v).image (fun x => f' x)).card =
          ((G.neighborFinset v).image (fun x => f x)).card := by
    intro v
    have hinj : Function.Injective (fun i : Fin (D * 3 - 1) => i.castLE hN) :=
      Fin.castLE_injective hN
    calc
      ((G.neighborFinset v).image (fun x => f' x)).card =
          (((G.neighborFinset v).image (fun x => f x)).image
              (fun i : Fin (D * 3 - 1) => i.castLE hN)).card := by
            -- rewrite the RHS using `image_image`
            simpa [f', Function.comp] using
              congrArg Finset.card
                ((Finset.image_image
                      (s := G.neighborFinset v)
                      (f := fun x => f x)
                      (g := fun i : Fin (D * 3 - 1) => i.castLE hN)).symm)
      _ = ((G.neighborFinset v).image (fun x => f x)).card := by
            simpa using
              (Finset.card_image_of_injective
                (s := (G.neighborFinset v).image (fun x => f x))
                (f := fun i : Fin (D * 3 - 1) => i.castLE hN) hinj)

  have hneigh :
      ∀ v : V,
        ((G.neighborFinset v).image (fun x => f x)).card ≥ min 3 (G.degree v) := by
    intro v
    have h := hneigh' v
    simpa [hcardEq v] using h

  refine ⟨f, ?_, ?_⟩
  · intro u v huv
    exact hproper_aux (LeanFun.Coloring.auxGraphC3_adj_of_adj (G := G) huv)
  · intro v
    simpa using (hneigh v)

end LeanFun.Coloring

