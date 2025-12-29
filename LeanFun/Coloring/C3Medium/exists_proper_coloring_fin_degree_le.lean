import Mathlib

namespace LeanFun.Coloring

theorem exists_proper_coloring_fin_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdeg : ∀ v : V, G.degree v ≤ D) :
    ∃ g : V → Fin (D + 1),
      (∀ ⦃u v : V⦄, G.Adj u v → g u ≠ g v) := by
  classical
  let P : Finset V → Prop := fun s =>
    ∃ g : V → Fin (D + 1),
      ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → G.Adj u v → g u ≠ g v
  have hP : P (Finset.univ : Finset V) := by
    refine Finset.induction_on (s := (Finset.univ : Finset V)) ?base ?step
    · refine ⟨fun _ => 0, ?_⟩
      intro u v hu hv huv
      have : False := by simpa using hu
      exact this.elim
    · intro a s ha hs
      rcases hs with ⟨g, hg⟩
      let forb : Finset (Fin (D + 1)) :=
        ((G.neighborFinset a).filter (fun v => v ∈ s)).image g
      have hforb_le : forb.card ≤ D := by
        calc
          forb.card
              ≤ ((G.neighborFinset a).filter (fun v => v ∈ s)).card := by
                simpa [forb] using
                  (Finset.card_image_le
                    (s := (G.neighborFinset a).filter (fun v => v ∈ s))
                    (f := g))
          _ ≤ (G.neighborFinset a).card := by
                simpa using
                  (Finset.card_filter_le (s := G.neighborFinset a)
                    (p := fun v => v ∈ s))
          _ = G.degree a := by
                simpa using
                  (G.card_neighborFinset_eq_degree (v := a))
          _ ≤ D := hdeg a
      have hforb_lt :
          forb.card < (Finset.univ : Finset (Fin (D + 1))).card := by
        have : forb.card < Fintype.card (Fin (D + 1)) := by
          simpa using (Nat.lt_succ_of_le hforb_le)
        simpa [Finset.card_univ] using this
      rcases Finset.exists_mem_notMem_of_card_lt_card (s := forb)
          (t := (Finset.univ : Finset (Fin (D + 1)))) hforb_lt with
        ⟨c, -, hc⟩
      let g' : V → Fin (D + 1) :=
        fun v => if v = a then c else g v
      refine ⟨g', ?_⟩
      intro u v hu hv huv
      by_cases huA : u = a
      · subst huA
        by_cases hvA : v = a
        · subst hvA
          have : False := (G.ne_of_adj huv) rfl
          exact this.elim
        ·
          have hvS : v ∈ s := by
            have : v = a ∨ v ∈ s := (Finset.mem_insert.1 hv)
            exact this.resolve_left hvA
          have hv_forb : g v ∈ forb := by
            have hv_neighbor : v ∈ G.neighborFinset a := by
              simpa using
                (G.mem_neighborFinset (v := a) (w := v)).2 huv
            have hv_filter :
                v ∈ (G.neighborFinset a).filter (fun w => w ∈ s) :=
              Finset.mem_filter.2 ⟨hv_neighbor, hvS⟩
            exact Finset.mem_image.2 ⟨v, hv_filter, rfl⟩
          have hcg : c ≠ g v := by
            intro hEq
            apply hc
            simpa [forb, hEq] using hv_forb
          simpa [g', hvA] using hcg
      ·
        by_cases hvA : v = a
        · subst hvA
          have huS : u ∈ s := by
            have : u = a ∨ u ∈ s := (Finset.mem_insert.1 hu)
            exact this.resolve_left huA
          have hu_forb : g u ∈ forb := by
            have hu_neighbor : u ∈ G.neighborFinset a := by
              have : G.Adj a u := G.symm huv
              simpa using
                (G.mem_neighborFinset (v := a) (w := u)).2 this
            have hu_filter :
                u ∈ (G.neighborFinset a).filter (fun w => w ∈ s) :=
              Finset.mem_filter.2 ⟨hu_neighbor, huS⟩
            exact Finset.mem_image.2 ⟨u, hu_filter, rfl⟩
          have hgc : g u ≠ c := by
            intro hEq
            apply hc
            have : c ∈ forb := by simpa [hEq] using hu_forb
            simpa using this
          simpa [g', huA] using hgc
        ·
          have huS : u ∈ s := by
            have : u = a ∨ u ∈ s := (Finset.mem_insert.1 hu)
            exact this.resolve_left huA
          have hvS : v ∈ s := by
            have : v = a ∨ v ∈ s := (Finset.mem_insert.1 hv)
            exact this.resolve_left hvA
          simpa [g', huA, hvA] using hg huS hvS huv
  rcases hP with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro u v huv
  simpa using hg (u := u) (v := v) (by simp) (by simp) huv

end LeanFun.Coloring

