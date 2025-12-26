import Mathlib
import LeanFun.Coloring.ColorIcc
import LeanFun.Coloring.FinToColorIccInjective
import LeanFun.Coloring.ExistsColoringC3Fin

namespace LeanFun

open scoped Classical

variable {V : Type*}

-- Proof provided by theorem prover; included verbatim.

theorem exists_coloring_c3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * c + 1
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        ∃ s : Finset V,
          s ⊆ G.neighborFinset v ∧
          s.card = k ∧
          (s.image (fun x => f x)).card = k) := by
  classical
  -- Unfold the `let`-bindings `c = 3` and `N = D * c + 1`.
  simp
  obtain ⟨g, hgProper, hgNeigh⟩ := by
    simpa using (exists_coloring_c3_fin (V := V) (G := G) D hD hdeg)
  let N : ℕ := D * 3 + 1
  -- Transport the coloring along the injective map `finToColorIcc`.
  let f : V → { n : ℕ // n ∈ Set.Icc (1 : ℕ) N } := fun v => finToColorIcc N (g v)
  refine ⟨f, ?_, ?_⟩
  · intro u v huv hEq
    apply hgProper huv
    -- Injectivity of `finToColorIcc` turns an equality of colors into an equality in `Fin N`.
    have : g u = g v := (finToColorIcc_injective N) (by simpa [f] using hEq)
    simpa [this]
  · intro v
    -- Reuse the witness finset from the `Fin N` statement.
    rcases (by
      -- `hgNeigh v` has the same `let k := ...` form.
      simpa [N] using hgNeigh v) with ⟨s, hsSub, hsCard, hsImgCard⟩
    refine ⟨s, hsSub, hsCard, ?_⟩
    -- The image cardinality is preserved under an injective map.
    have hcard : (s.image (fun x => f x)).card = (s.image (fun x => g x)).card := by
      -- Rewrite the image under a composition.
      have himage : s.image (fun x => f x) = (s.image (fun x => g x)).image (finToColorIcc N) := by
        ext y
        simp [f]
      -- Now use injectivity to compare the cardinals.
      -- (The codomain has decidable equality since it is a subtype of `ℕ`.)
      simpa [himage] using
        (Finset.card_image_of_injective (s := s.image (fun x => g x))
          (f := finToColorIcc N) (finToColorIcc_injective N))
    -- Finish with the corresponding statement for `g`.
    exact hcard.trans hsImgCard

end LeanFun
