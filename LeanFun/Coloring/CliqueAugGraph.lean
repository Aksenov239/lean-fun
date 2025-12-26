import Mathlib

namespace LeanFun

open scoped Classical

variable {V : Type*}

/-- The graph obtained from `G` by adding cliques on the vertex sets `T v`. -/
@[simp] def cliqueAugGraph (G : SimpleGraph V) (T : V → Finset V) : SimpleGraph V :=
  { Adj := fun x y => G.Adj x y ∨ ∃ v, x ∈ T v ∧ y ∈ T v ∧ x ≠ y
    symm := by
      intro x y hxy
      rcases hxy with hxy | hxy
      · exact Or.inl (G.adj_symm hxy)
      · rcases hxy with ⟨v, hxTv, hyTv, hne⟩
        exact Or.inr ⟨v, hyTv, hxTv, Ne.symm hne⟩
    loopless := by
      intro x hxx
      rcases hxx with hxx | hxx
      · exact G.loopless x hxx
      · rcases hxx with ⟨v, hxTv, hxTv', hne⟩
        exact hne rfl }

end LeanFun
