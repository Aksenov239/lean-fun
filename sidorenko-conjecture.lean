import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finite.Card
import Mathlib.Data.Real.Basic

/--
Sidorenko's conjecture (counting form).

For any bipartite simple graph `H` and any simple graph `G`,
the number of graph homomorphisms `H →g G` is at least

`( (2 * |E(G)|) / |V(G)|^2 ) ^ |E(H)| * |V(G)| ^ |V(H)|`.

Here `|E(G)|` is `Nat.card (↑G.edgeSet)` and `|V(G)|` is `Nat.card V_G`.
-/
theorem SidorenkoConjecture:
  ∀ {V_H V_G : Type*} [Fintype V_H] [Fintype V_G]
  (H : SimpleGraph V_H) (G : SimpleGraph V_G),
  H.IsBipartite →
    ( (Nat.card (H →g G) : ℝ) ≥
      (( (2 * (Nat.card (↑G.edgeSet) : ℝ))
            / ((Nat.card V_G : ℝ) ^ (2 : Nat)) ) ^ (Nat.card (↑H.edgeSet))) *
            ((Nat.card V_G : ℝ) ^ (Nat.card V_H)) ) :=
    sorry
