import LeanFun.Coloring.Base

namespace LeanFun.Coloring

theorem auxGraphC3_adj_of_mem_Tmin3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {w u v : V} :
    u ∈ Tmin3 G w → v ∈ Tmin3 G w → u ≠ v →
      (auxGraphC3 G).Adj u v := by
  intro hu hv hne
  exact Or.inr ⟨w, hu, hv, hne⟩

end LeanFun.Coloring
