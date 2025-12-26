import LeanFun.Coloring.SimpleGraph_colorable_of_forall_finset_exists_degree_lt
import LeanFun.Coloring.auxGraphC3_exists_low_degree_in_induce

namespace LeanFun.Coloring

theorem auxGraphC3_colorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ)
    (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    (auxGraphC3 G).Colorable (D * 3) := by
  classical
  haveI : DecidableRel (auxGraphC3 G).Adj := by
    classical
    exact Classical.decRel (auxGraphC3 G).Adj

  have hlow :
      ∀ s : Finset V, s.Nonempty →
        ∃ v ∈ s, ((auxGraphC3 G).neighborFinset v ∩ s).card < D * 3 :=
    auxGraphC3_exists_low_degree_in_induce (G := G) (D := D) (hD := hD) (hdeg := hdeg)

  simpa using
    (SimpleGraph_colorable_of_forall_finset_exists_degree_lt
      (G := auxGraphC3 G) (n := D * 3) hlow)

end LeanFun.Coloring

