import LeanFun.Coloring.auxGraphC3_adj_of_adj

namespace LeanFun.Coloring

theorem auxGraphC3_neighborFinset_superset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel (auxGraphC3 G).Adj] (v : V) :
    G.neighborFinset v ⊆ (auxGraphC3 G).neighborFinset v := by
  classical
  intro x hx
  have hxadj : G.Adj v x := by
    simpa [SimpleGraph.mem_neighborFinset] using hx
  have hxadj' : (auxGraphC3 G).Adj v x := auxGraphC3_adj_of_adj (G := G) hxadj
  simpa [SimpleGraph.mem_neighborFinset] using hxadj'

end LeanFun.Coloring

