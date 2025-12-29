import LeanFun.Coloring.C3Medium.exists_coloring_c3_medium_fin

namespace LeanFun.Coloring

theorem exists_coloring_fin_c3 {V : Type*} [Fintype V] [DecidableEq V]
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
        ((G.neighborFinset v).image f).card ≥ k) := by
  classical
  simp (config := { zeta := true })
  simpa using
    (LeanFun.Coloring.exists_coloring_c3_medium_fin (G := G) (D := D) hD hdeg)

end LeanFun.Coloring
