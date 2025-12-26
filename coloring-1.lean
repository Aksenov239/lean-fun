import Mathlib

open scoped BigOperators

theorem exists_coloring_c3
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 3
    let N : ℕ := D * (c - 1) + 1
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        ∃ s : Finset V,
          s ⊆ G.neighborFinset v ∧
          s.card = k ∧
          (s.image (fun x => f x)).card = k) :=
  -- proof goes here
  sorry

theorem exists_coloring_c4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (4 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    let c : ℕ := 4
    let N : ℕ := D * (c - 1) + 1
    ∃ f : V → {n : ℕ // n ∈ Set.Icc (1 : ℕ) N},
      (∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ∧
      (∀ v : V,
        let k : ℕ := min c (G.degree v)
        ∃ s : Finset V,
          s ⊆ G.neighborFinset v ∧
          s.card = k ∧
          (s.image (fun x => f x)).card = k) :=
  -- proof goes here
  sorry
