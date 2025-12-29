import Mathlib
import LeanFun.Coloring.C3Medium.auxGraphC3_sum_extra_neighbors_in_s_le

namespace LeanFun.Coloring

theorem auxGraphC3_exists_low_degree_in_induce_medium {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : (2 : ℕ) ^ (3 : ℕ) ≤ D)
    (hdeg : ∀ v : V, G.degree v ≤ D)
    [DecidableRel (LeanFun.Coloring.auxGraphC3 G).Adj] :
    ∀ s : Finset V, s.Nonempty →
      ∃ v ∈ s,
        (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v) ∩ s).card < D * 3 - 1 := by
  intro s hs
  classical
  let H : SimpleGraph V := LeanFun.Coloring.auxGraphC3 G
  let N : ℕ := D * 3 - 1
  by_contra hno
  have hbig :
      ∀ v ∈ s, N ≤ ((H.neighborFinset v) ∩ s).card := by
    intro v hv
    by_contra hNv
    apply hno
    refine ⟨v, hv, ?_⟩
    have : ((H.neighborFinset v) ∩ s).card < N := lt_of_not_ge hNv
    simpa [H, N] using this
  have hLower :
      s.card * N ≤ ∑ v ∈ s, ((H.neighborFinset v) ∩ s).card := by
    calc
      s.card * N = ∑ _v ∈ s, N := by simp [N]
      _ ≤ ∑ v ∈ s, ((H.neighborFinset v) ∩ s).card := by
        refine Finset.sum_le_sum ?_
        intro v hv
        exact hbig v hv
  have hCard_le :
      ∀ v ∈ s,
        ((H.neighborFinset v) ∩ s).card ≤
          (G.neighborFinset v).card +
            (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card) := by
    intro v hv
    have hsubset :
        (H.neighborFinset v ∩ s) ⊆
          (G.neighborFinset v ∪
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s)) := by
      intro x hx
      have hxH :
          x ∈ H.neighborFinset v := (Finset.mem_inter.1 hx).1
      have hxS : x ∈ s := (Finset.mem_inter.1 hx).2
      by_cases hxG : x ∈ G.neighborFinset v
      · exact Finset.mem_union.2 (Or.inl hxG)
      ·
        have hxDiff : x ∈ (H.neighborFinset v \ G.neighborFinset v) := by
          exact Finset.mem_sdiff.2 ⟨hxH, hxG⟩
        have hxExtra :
            x ∈ ((H.neighborFinset v \ G.neighborFinset v) ∩ s) := by
          exact Finset.mem_inter.2 ⟨hxDiff, hxS⟩
        exact Finset.mem_union.2 (Or.inr hxExtra)
    have h1 :
        ((H.neighborFinset v) ∩ s).card ≤
          (G.neighborFinset v ∪
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s)).card :=
      Finset.card_le_card hsubset
    have h2 :
        (G.neighborFinset v ∪
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s)).card ≤
          (G.neighborFinset v).card +
            ((H.neighborFinset v \ G.neighborFinset v) ∩ s).card := by
      simpa using
        (Finset.card_union_le (G.neighborFinset v)
          ((H.neighborFinset v \ G.neighborFinset v) ∩ s))
    exact le_trans h1 h2
  have hUpper :
      (∑ v ∈ s, ((H.neighborFinset v) ∩ s).card) ≤ s.card * (D + 8) := by
    have hSum_le :
        (∑ v ∈ s, ((H.neighborFinset v) ∩ s).card) ≤
          ∑ v ∈ s,
            ((G.neighborFinset v).card +
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) := by
      refine Finset.sum_le_sum ?_
      intro v hv
      exact hCard_le v hv
    have hSum_le' :
        (∑ v ∈ s, ((H.neighborFinset v) ∩ s).card) ≤
          (∑ v ∈ s, (G.neighborFinset v).card) +
            (∑ v ∈ s,
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) := by
      simpa [Finset.sum_add_distrib] using hSum_le
    have hSumG :
        (∑ v ∈ s, (G.neighborFinset v).card) ≤ s.card * D := by
      have hSumG' :
          (∑ v ∈ s, (G.neighborFinset v).card) ≤ ∑ _v ∈ s, D := by
        refine Finset.sum_le_sum ?_
        intro v hv
        calc
          (G.neighborFinset v).card = G.degree v := by
            simpa using
              (SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v))
          _ ≤ D := hdeg v
      simpa using hSumG'
    have hSumExtra :
        (∑ v ∈ s,
            (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) ≤
          8 * s.card := by
      have h' :
          (∑ v ∈ s,
              (((LeanFun.Coloring.auxGraphC3 G).neighborFinset v \ G.neighborFinset v) ∩ s).card) ≤
            8 * s.card :=
        auxGraphC3_sum_extra_neighbors_in_s_le (G := G) (D := D) (hdeg := hdeg)
          (s := s)
          (hbig :=
            by
              intro v hv
              simpa [H, N] using hbig v hv)
      simpa [H] using h'
    have hSumTotal :
        (∑ v ∈ s, (G.neighborFinset v).card) +
            (∑ v ∈ s,
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) ≤
          s.card * D + 8 * s.card :=
      add_le_add hSumG hSumExtra
    have hSumTotal' :
        (∑ v ∈ s, (G.neighborFinset v).card) +
            (∑ v ∈ s,
              (((H.neighborFinset v \ G.neighborFinset v) ∩ s).card)) ≤
          s.card * (D + 8) := by
      simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSumTotal
    exact le_trans hSum_le' hSumTotal'
  have hD8 : 8 ≤ D := by
    simpa using hD
  have hspos : 0 < s.card := by
    exact (Finset.card_pos.2 hs)
  have hDpluslt : D + 8 < N := by
    have h16le2D : 16 ≤ 2 * D := by
      have := Nat.mul_le_mul_left 2 hD8
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
    have h9lt16 : 9 < 16 := by decide
    have h9lt2D : 9 < 2 * D := lt_of_lt_of_le h9lt16 h16le2D
    have hD9ltD2D : D + 9 < D + 2 * D := Nat.add_lt_add_left h9lt2D D
    have hD9lt3D : D + 9 < D * 3 := by
      have hEq : D + 2 * D = D * 3 := by ring
      exact lt_of_lt_of_eq hD9ltD2D hEq
    have hAdd : D + 8 + 1 < D * 3 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hD9lt3D
    have : D + 8 < D * 3 - 1 := lt_tsub_of_add_lt_right hAdd
    simpa [N] using this
  have hMul_lt : s.card * (D + 8) < s.card * N :=
    Nat.mul_lt_mul_of_pos_left hDpluslt hspos
  have hLe : s.card * N ≤ s.card * (D + 8) :=
    le_trans hLower hUpper
  exact (not_lt_of_ge hLe) hMul_lt

end LeanFun.Coloring

