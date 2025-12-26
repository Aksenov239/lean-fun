import LeanFun.Coloring.Tmin3_subset_neighborFinset
import LeanFun.Coloring.Tmin3_card
import LeanFun.Coloring.auxGraphC3_adj_of_mem_Tmin3

namespace LeanFun.Coloring

theorem auxGraphC3_neighbor_image_card_ge_min3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} (hdeg : ∀ v : V, G.degree v ≤ D) :
    let N : ℕ := D * 3
    ∀ (f : V → Fin N),
      (∀ ⦃u v : V⦄, (auxGraphC3 G).Adj u v → f u ≠ f v) →
      (∀ v : V, ((G.neighborFinset v).image (fun x => f x)).card ≥ min 3 (G.degree v)) := by
  classical
  dsimp
  intro f hfproper v
  -- Define T as a subset of neighbors of v of size min 3 (deg v)
  let T : Finset V := Tmin3 G v
  have hTsub : T ⊆ G.neighborFinset v := by
    simpa [T] using (Tmin3_subset_neighborFinset (G := G) v)
  have hTinjon : Set.InjOn (fun x => f x) (T : Set V) := by
    intro x hx y hy hxy
    by_contra hne
    have hx' : x ∈ Tmin3 G v := by
      simpa [T] using hx
    have hy' : y ∈ Tmin3 G v := by
      simpa [T] using hy
    have hadj : (auxGraphC3 G).Adj x y :=
      auxGraphC3_adj_of_mem_Tmin3 (G := G) (w := v) hx' hy' hne
    exact (hfproper hadj) hxy
  have hcard_image : (T.image (fun x => f x)).card = T.card := by
    -- use the characterization of card(image) via InjOn
    exact (Finset.card_image_iff).2 hTinjon
  have himage_sub : T.image (fun x => f x) ⊆ (G.neighborFinset v).image (fun x => f x) :=
    Finset.image_subset_image hTsub
  have hcard_le : (T.image (fun x => f x)).card ≤ ((G.neighborFinset v).image (fun x => f x)).card :=
    Finset.card_le_card himage_sub
  have hTle : T.card ≤ ((G.neighborFinset v).image (fun x => f x)).card := by
    simpa [hcard_image] using hcard_le
  have hTcard : T.card = min 3 (G.degree v) := by
    simpa [T] using (Tmin3_card (G := G) v)
  -- conclude by comparing with the image of T
  have : min 3 (G.degree v) ≤ ((G.neighborFinset v).image (fun x => f x)).card := by
    -- rewrite `min 3 (deg v)` as `T.card`
    simpa [hTcard] using hTle
  exact this

end LeanFun.Coloring
