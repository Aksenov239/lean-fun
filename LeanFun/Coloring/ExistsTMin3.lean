import Mathlib

namespace LeanFun

open scoped Classical

variable {V : Type*}

-- Proof provided by theorem prover; included verbatim.

theorem exists_T_min3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ T : V → Finset V,
      ∀ v : V,
        T v ⊆ G.neighborFinset v ∧
        (T v).card = min 3 (G.degree v) := by
  classical
  have h_exists : ∀ v : V,
      ∃ t : Finset V, t ⊆ G.neighborFinset v ∧ t.card = min 3 (G.degree v) := by
    intro v
    have hn : min 3 (G.degree v) ≤ (G.neighborFinset v).card := by
      -- rewrite the right-hand side using the fact that card neighborFinset = degree
      -- and use `min_le_right`
      simpa [G.card_neighborFinset_eq_degree] using (Nat.min_le_right 3 (G.degree v))
    rcases Finset.exists_subset_card_eq (s := G.neighborFinset v)
        (n := min 3 (G.degree v)) hn with ⟨t, ht, hcard⟩
    refine ⟨t, ht, ?_⟩
    simpa using hcard
  choose T hT using h_exists
  refine ⟨T, ?_⟩
  intro v
  simpa using hT v

end LeanFun
