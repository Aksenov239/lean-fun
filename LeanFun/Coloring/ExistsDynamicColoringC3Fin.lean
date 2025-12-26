import Mathlib
import LeanFun.Coloring.CliqueAugGraph
import LeanFun.Coloring.ExistsProperColoringOfDegreeLe
import LeanFun.Coloring.ExistsTMin3
import LeanFun.Coloring.CliqueAugGraphDegreeLe

namespace LeanFun

open scoped Classical

variable {V : Type*}

-- Proof provided by theorem prover; included verbatim.

theorem exists_dynamic_coloring_c3_fin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    ∃ f : V → Fin (D * 3 + 1),
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V, min 3 (G.degree v) ≤ ((G.neighborFinset v).image f).card) := by
  classical
  -- Step 1: choose the neighbor subsets `T v` of size `min 3 (G.degree v)`.
  rcases exists_T_min3 (G := G) with ⟨T, hT⟩
  have hTsub : ∀ v : V, T v ⊆ G.neighborFinset v := by
    intro v
    exact (hT v).1
  have hTcardEq : ∀ v : V, (T v).card = min 3 (G.degree v) := by
    intro v
    exact (hT v).2

  -- Step 2: define the augmented graph `H`.
  let H : SimpleGraph V := cliqueAugGraph G T
  -- We will use decidable adjacency on `H` (classical).
  letI : DecidableRel H.Adj := by
    classical
    infer_instance

  -- Step 3: from `hTcardEq`, get the uniform bound `(T v).card ≤ 3`.
  have hTcard : ∀ v : V, (T v).card ≤ 3 := by
    intro v
    -- rewrite by the defining cardinality and use `min ≤ left`.
    rw [hTcardEq v]
    exact Nat.min_le_left 3 (G.degree v)

  -- Step 4: bound the degrees in `H`.
  have hdegH : ∀ x : V, H.degree x ≤ D * 3 := by
    -- This is exactly the provided helper lemma.
    simpa [H] using
      (cliqueAugGraph_degree_le (G := G) (T := T) (hTsub := hTsub) (hTcard := hTcard)
        (D := D) (hdeg := hdeg))

  -- Step 5: proper coloring of `H` with `D*3+1` colors.
  rcases
      exists_proper_coloring_of_degree_le (H := H) (m := D * 3) (hdeg := hdegH)
    with ⟨f, hfproperH⟩

  -- Step 6-7: transfer properness to `G` and prove the dynamic lower bound.
  refine ⟨f, ?_, ?_⟩
  · intro u v huv
    apply hfproperH
    exact Or.inl huv
  · intro v
    -- `f` is injective on `T v` since `T v` is a clique in `H`.
    have hinj : Set.InjOn f (T v) := by
      intro a ha b hb hab
      by_contra hne
      have hAdj : H.Adj a b := Or.inr ⟨v, ha, hb, hne⟩
      exact (hfproperH hAdj) hab
    have hcard_img : ((T v).image f).card = (T v).card := by
      simpa using (Finset.card_image_of_injOn (s := T v) (f := f) hinj)

    -- Compare the image of `T v` with the image of the full neighbor set.
    have hsubset_img : (T v).image f ⊆ (G.neighborFinset v).image f := by
      intro x hx
      rcases Finset.mem_image.1 hx with ⟨a, haT, rfl⟩
      have haN : a ∈ G.neighborFinset v := hTsub v haT
      exact Finset.mem_image.2 ⟨a, haN, rfl⟩
    have hcard_le : ((T v).image f).card ≤ ((G.neighborFinset v).image f).card :=
      Finset.card_le_card hsubset_img

    -- Assemble the inequality.
    calc
      min 3 (G.degree v) = (T v).card := (hTcardEq v).symm
      _ = ((T v).image f).card := hcard_img.symm
      _ ≤ ((G.neighborFinset v).image f).card := hcard_le

end LeanFun
