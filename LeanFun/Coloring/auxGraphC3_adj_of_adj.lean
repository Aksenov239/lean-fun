import LeanFun.Coloring.Base

namespace LeanFun.Coloring

theorem auxGraphC3_adj_of_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} :
    G.Adj u v → (auxGraphC3 G).Adj u v := by
  intro h
  exact Or.inl h

end LeanFun.Coloring
