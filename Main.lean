import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Interval

namespace ListNondegenerate

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-! ## Neighborhood and degree -/

/-- `Ne(G,v)` as a finset of neighbors of `v`. -/
noncomputable def Ne (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => G.Adj v w)

/-- `deg(G,v)` as the cardinality of `Ne(G,v)`. -/
noncomputable def deg (v : V) : ℕ :=
  (Ne (G := G) v).card

/-! ## Global palette, list systems, and list colorings

The Russian statement uses the palette `{1,2,...,l}` where `l = |V(G)| * C`.
Here we model a palette of size `l` by the type `Fin l` (i.e. `{0,1,...,l-1}`),
which is equivalent for existence statements.
-/

/-- Global palette of size `l = |V| * C`. -/
def Palette (C : ℕ) : Type :=
  Fin (Fintype.card V * C)

/-- A list system is a map `L : V → Finset (Palette C)`. -/
def ListSystem (C : ℕ) : Type :=
  V → Finset (Palette (V := V) C)

/-- The condition `|L(v)| = C` for every vertex. -/
def ListSystemHasCard {C : ℕ} (L : ListSystem (V := V) C) : Prop :=
  ∀ v : V, (L v).card = C

/-- A list system is *trivial* if all lists are equal. -/
def ListSystemTrivial {C : ℕ} (L : ListSystem (V := V) C) : Prop :=
  ∃ S : Finset (Palette (V := V) C), ∀ v : V, L v = S

/-- A coloring is a function `y : V → Palette C`. -/
abbrev Coloring (C : ℕ) : Type :=
  V → Palette (V := V) C

/-- `y` is a list-coloring w.r.t. `L` if `y(v) ∈ L(v)` for all `v`. -/
def IsListColoring {C : ℕ} (L : ListSystem (V := V) C) (y : Coloring (V := V) C) : Prop :=
  ∀ v : V, y v ∈ L v

/-- Properness: adjacent vertices receive different colors. -/
def IsProper {C : ℕ} (y : Coloring (V := V) C) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → y u ≠ y v

/-! ## (c,p)-nondegeneracy and f-nondegeneracy -/

/-- “`y` is injective on the finite set `W`” (written out without `Set.InjOn`). -/
def InjOnFinset {α : Type} (y : V → α) (W : Finset V) : Prop :=
  ∀ ⦃u : V⦄, u ∈ W →
    ∀ ⦃w : V⦄, w ∈ W → y u = y w → u = w

/--
`(c,p)`-nondegenerate: for every `v` with `deg(v) ≥ p`,
there is a subset `W ⊆ Ne(v)` with `|W| ≥ c` and `y` injective on `W`.
-/
def Nondegenerate {C : ℕ} (y : Coloring (V := V) C) (c p : ℕ) : Prop :=
  ∀ v : V, deg (G := G) v ≥ p →
    ∃ W : Finset V,
      W ⊆ Ne (G := G) v ∧
      c ≤ W.card ∧
      InjOnFinset (V := V) y W

/-- `f`-nondegenerate: nondegenerate for every pair `(cᵢ,pᵢ) ∈ f`. -/
def FNondegenerate {C : ℕ} (y : Coloring (V := V) C) (f : Finset (ℕ × ℕ)) : Prop :=
  ∀ cp ∈ f, Nondegenerate (G := G) y cp.1 cp.2

/-- `Lin(c) = {(2,2),(3,3),...,(c,c)}` as a finset. -/
def Lin (c : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).image (fun k => (k, k))

/--
`Quad(c)` as written in the text: `(k, k^2 - k)` for `k = 2..c`
(i.e. `(k, k*(k-1))`).
Note: the example `(4,10)` in the Russian text would not match `k^2-k` (it would be `12`),
so that example seems to be a typo; this definition follows the formula `c^2 - c`.
-/
def Quad (c : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).image (fun k => (k, k*k - k))

/-! ## The theorem statement (no proof) -/

/--
**Theorem (formal statement only).**

If `c ≥ 2` and
`C = max (D + c*c - 1) ((D+1)*(c-1))`,
and the maximum degree of `G` is at most `D`,
then for *every* list system `L` with lists of size `C`,
there exists a proper list-coloring which is `Lin(c)`-nondegenerate.
-/
theorem exists_proper_list_coloring_Lin
    {D C c : ℕ}
    (hc : 2 ≤ c)
    (hC : C = max (D + c * c - 1) ((D + 1) * (c - 1)))
    (hΔ : ∀ v : V, deg (G := G) v ≤ D) :
    ∀ (L : ListSystem (V := V) C),
      ListSystemHasCard (V := V) (C := C) L →
      ∃ (y : Coloring (V := V) C),
        IsListColoring (V := V) (C := C) L y ∧
        IsProper (G := G) (V := V) (C := C) y ∧
        FNondegenerate (G := G) (V := V) (C := C) y (Lin c) :=
by
  -- proof not provided (translation only)
  sorry

/--
**Theorem 2 (formal statement only).**

If `c ≥ 2` and `C = D + c*c - 1` and `Δ(G) ≤ D`,
then for every list system with lists of size `C`
there exists a proper `Quad(c)`-nondegenerate list-coloring.
-/
theorem exists_proper_list_coloring_Quad
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    {D C c : ℕ}
    (hc : 2 ≤ c)
    (hC : C = D + c * c - 1)
    (hΔ : ∀ v : V, deg (G := G) v ≤ D) :
    ∀ (L : ListSystem (V := V) C),
      ListSystemHasCard (V := V) (C := C) L →
      ∃ (y : Coloring (V := V) C),
        IsListColoring (V := V) (C := C) L y ∧
        IsProper (G := G) y ∧
        FNondegenerate (G := G) (V := V) (C := C) y (Quad c) :=
by
  -- proof not provided (formalization only)
  sorry

/-- A minimal bipartiteness predicate: existence of a proper 2-coloring by `Bool`. -/
def IsBipartite {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ b : V → Bool, ∀ ⦃u v : V⦄, G.Adj u v → b u ≠ b v

/--
**Theorem 3 (formal statement only).**

For every `c ≥ 2` and every `N ≥ 2`, there exists `D ≥ N` and a finite bipartite graph `G`
with `deg(G,v) ≤ D` for all `v`, such that if `C = (c-1)*D` then for every *trivial*
list system `L` with lists of size `C`, there is **no** proper `Lin(c)`-nondegenerate
list-coloring of `G`.
-/

theorem exists_bipartite_counterexample_Lin_trivial
    (c N : ℕ) (hc : 2 ≤ c) (hN : 2 ≤ N) :
    ∃ D : ℕ, N ≤ D ∧
      ∃ (V : Type) (instF : Fintype V) (instDE : DecidableEq V),
      (letI : Fintype V := instF
       letI : DecidableEq V := instDE
        ∃ (G : SimpleGraph V),
          IsBipartite G ∧
          (∀ v : V, deg (G := G) v ≤ D) ∧
          let C : ℕ := (c - 1) * D
          ∀ (L : ListSystem (V := V) C),
              ListSystemHasCard (V := V) (C := C) L →
              ListSystemTrivial (V := V) (C := C) L →
              ¬ ∃ (y : Coloring (V := V) C),
                  IsListColoring (V := V) (C := C) L y ∧
                  IsProper (G := G) y ∧
                  FNondegenerate (G := G) (V := V) (C := C) y (Lin c)) :=
by
  -- proof not provided (formalization only)
  sorry

end ListNondegenerate
