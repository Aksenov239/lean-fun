import Mathlib
import LeanFun.Coloring.CliqueAugGraph

namespace LeanFun

open scoped Classical

variable {V : Type*}

-- Proof provided by theorem prover; included verbatim.

theorem cliqueAugGraph_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : V → Finset V) [DecidableRel (cliqueAugGraph G T).Adj]
    (hTsub : ∀ v : V, T v ⊆ G.neighborFinset v)
    (hTcard : ∀ v : V, (T v).card ≤ 3)
    (D : ℕ)
    (hdeg : ∀ v : V, G.degree v ≤ D) :
    ∀ x : V, (cliqueAugGraph G T).degree x ≤ D * 3 := by
  intro x
  classical
  let Ix : Finset V := (G.neighborFinset x).filter (fun v => x ∈ T v)
  let extra : Finset V := Ix.biUnion (fun v => (T v).erase x)
  have hsubset : (cliqueAugGraph G T).neighborFinset x ⊆ (G.neighborFinset x) ∪ extra := by
    intro y hy
    have hyAdj : (cliqueAugGraph G T).Adj x y :=
      (SimpleGraph.mem_neighborFinset (G := cliqueAugGraph G T) (v := x) (w := y)).1 hy
    rcases hyAdj with hyG | hyT
    · have hyGmem : y ∈ G.neighborFinset x :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := x) (w := y)).2 hyG
      exact Finset.mem_union.2 (Or.inl hyGmem)
    · rcases hyT with ⟨v, hxTv, hyTv, hxy⟩
      have hxNbr : x ∈ G.neighborFinset v := hTsub v hxTv
      have hAdj_vx : G.Adj v x :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := v) (w := x)).1 hxNbr
      have hAdj_xv : G.Adj x v := G.adj_symm hAdj_vx
      have hvNbr : v ∈ G.neighborFinset x :=
        (SimpleGraph.mem_neighborFinset (G := G) (v := x) (w := v)).2 hAdj_xv
      have hvIx : v ∈ Ix := by
        exact Finset.mem_filter.2 ⟨hvNbr, hxTv⟩
      have hyErase : y ∈ (T v).erase x := by
        exact (Finset.mem_erase).2 ⟨Ne.symm hxy, hyTv⟩
      have hyExtra : y ∈ extra := by
        exact (Finset.mem_biUnion).2 ⟨v, hvIx, hyErase⟩
      exact Finset.mem_union.2 (Or.inr hyExtra)

  have hIx_le : Ix.card ≤ (G.neighborFinset x).card := by
    simpa [Ix] using
      (Finset.card_filter_le (G.neighborFinset x) (fun v => x ∈ T v))

  have hErase_le : ∀ v ∈ Ix, ((T v).erase x).card ≤ 2 := by
    intro v hv
    have hxTv : x ∈ T v := by
      have hv' : v ∈ (G.neighborFinset x).filter (fun v => x ∈ T v) := by
        simpa [Ix] using hv
      exact (Finset.mem_filter.1 hv').2
    rw [Finset.card_erase_of_mem hxTv]
    have h1 : (T v).card - 1 ≤ 3 - 1 := Nat.sub_le_sub_right (hTcard v) 1
    have h2 : 3 - 1 ≤ 2 := by decide
    exact le_trans h1 h2

  have hExtra_le : extra.card ≤ Ix.card * 2 := by
    simpa [extra] using
      (Finset.card_biUnion_le_card_mul Ix (fun v => (T v).erase x) 2 hErase_le)

  have hExtra_le' : extra.card ≤ (G.neighborFinset x).card * 2 := by
    exact le_trans hExtra_le (Nat.mul_le_mul_right 2 hIx_le)

  have hcard_neighbor : ((cliqueAugGraph G T).neighborFinset x).card ≤ (G.neighborFinset x).card * 3 := by
    have hcard_le_union : ((cliqueAugGraph G T).neighborFinset x).card ≤ ((G.neighborFinset x) ∪ extra).card := by
      exact Finset.card_le_card hsubset
    have hcard_union : ((G.neighborFinset x) ∪ extra).card ≤ (G.neighborFinset x).card + extra.card := by
      simpa using (Finset.card_union_le (G.neighborFinset x) extra)
    have hcard_le_sum : ((cliqueAugGraph G T).neighborFinset x).card ≤ (G.neighborFinset x).card + extra.card :=
      le_trans hcard_le_union hcard_union
    have hcard_le_sum' : ((cliqueAugGraph G T).neighborFinset x).card ≤ (G.neighborFinset x).card + (G.neighborFinset x).card * 2 := by
      exact le_trans hcard_le_sum (Nat.add_le_add_left hExtra_le' (G.neighborFinset x).card)
    calc
      ((cliqueAugGraph G T).neighborFinset x).card
          ≤ (G.neighborFinset x).card + (G.neighborFinset x).card * 2 := hcard_le_sum'
      _ = (G.neighborFinset x).card * 3 := by
        ring

  have hmul : (G.neighborFinset x).card * 3 ≤ D * 3 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using
      (Nat.mul_le_mul_right 3 (hdeg x))

  have hcard_final : ((cliqueAugGraph G T).neighborFinset x).card ≤ D * 3 :=
    le_trans hcard_neighbor hmul

  simpa [SimpleGraph.card_neighborFinset_eq_degree] using hcard_final

end LeanFun
