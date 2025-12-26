import LeanFun.Coloring.auxGraphC3_adj_of_adj
import LeanFun.Coloring.auxGraphC3_neighbor_image_card_ge_min3
import LeanFun.Coloring.auxGraphC3_colorable

namespace LeanFun.Coloring

theorem exists_coloring_fin_c3_simple {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * c
    ∃ f : V → Fin N,
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        let s := G.neighborFinset v
        (s.image (fun x => f x)).card >= k) := by
  classical
  -- Unfold the abbreviations `c` and `N`.
  dsimp
  have hc : (auxGraphC3 G).Colorable (D * 3) :=
    auxGraphC3_colorable (G := G) (D := D) (hD := hD) (hdeg := hdeg)
  let C : (auxGraphC3 G).Coloring (Fin (D * 3)) := hc.some
  let f : V → Fin (D * 3) := fun v => C v
  have hproper_aux : ∀ ⦃u v : V⦄, (auxGraphC3 G).Adj u v → f u ≠ f v := by
    intro u v huv
    simpa [f] using (C.valid huv)
  have hneigh :
      ∀ v : V,
        ((G.neighborFinset v).image (fun x => f x)).card ≥ min 3 (G.degree v) := by
    simpa using
      (auxGraphC3_neighbor_image_card_ge_min3 (G := G) (D := D) hdeg f hproper_aux)
  refine ⟨f, ?_, ?_⟩
  · intro u v huv
    exact hproper_aux (auxGraphC3_adj_of_adj (G := G) huv)
  · intro v
    simpa using (hneigh v)

end LeanFun.Coloring

