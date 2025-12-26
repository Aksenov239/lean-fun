import LeanFun.Coloring.Medium.auxGraphC3_exists_low_degree_in_induce_medium
import LeanFun.Coloring.SimpleGraph_colorable_of_forall_finset_exists_degree_lt

namespace LeanFun.Coloring

theorem auxGraphC3_colorable_medium {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    (LeanFun.Coloring.auxGraphC3 G).Colorable (D * 3 - 1) := by
  classical
  let H : SimpleGraph V := LeanFun.Coloring.auxGraphC3 G
  haveI : DecidableRel H.Adj := Classical.decRel _
  have hlow : ∀ s : Finset V, s.Nonempty →
      ∃ v ∈ s, ((H.neighborFinset v ∩ s).card < D * 3 - 1) := by
    intro s hs
    simpa [H] using
      (auxGraphC3_exists_low_degree_in_induce_medium (G := G) (D := D) hD hdeg s hs)
  simpa [H] using
    (LeanFun.Coloring.SimpleGraph_colorable_of_forall_finset_exists_degree_lt
      (G := H) (n := D * 3 - 1) hlow)

end LeanFun.Coloring

