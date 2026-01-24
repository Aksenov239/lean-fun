import Mathlib

def ListNondegenerate.InjOnFinset {V α : Type}
    (y : V → α) (W : Finset V) : Prop :=
  ∀ ⦃u : V⦄, u ∈ W →
    ∀ ⦃w : V⦄, w ∈ W → y u = y w → u = w

def ListNondegenerate.Lin (c : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).image (fun k => (k, k))

noncomputable def ListNondegenerate.Ne {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => G.Adj v w)

def ListNondegenerate.Palette {V : Type} [Fintype V] (C : ℕ) : Type :=
  Fin (Fintype.card V * C)

def ListNondegenerate.Coloring {V : Type} [Fintype V] (C : ℕ) : Type :=
  V → ListNondegenerate.Palette (V := V) C

def ListNondegenerate.IsProper {V : Type} [Fintype V]
    (G : SimpleGraph V) {C : ℕ} (y : ListNondegenerate.Coloring (V := V) C) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → y u ≠ y v

def ListNondegenerate.IsProperOn {V : Type} [Fintype V]
    (G : SimpleGraph V) {C : ℕ}
    (y : ListNondegenerate.Coloring (V := V) C) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → G.Adj u v → y u ≠ y v

def ListNondegenerate.ListSystem {V : Type} [Fintype V] (C : ℕ) : Type :=
  V → Finset (ListNondegenerate.Palette (V := V) C)

def ListNondegenerate.IsListColoring {V : Type} [Fintype V] {C : ℕ}
    (L : ListNondegenerate.ListSystem (V := V) C)
    (y : ListNondegenerate.Coloring (V := V) C) : Prop :=
  ∀ v : V, y v ∈ L v

def ListNondegenerate.IsListColoringOn {V : Type} [Fintype V] {C : ℕ}
    (L : ListNondegenerate.ListSystem (V := V) C)
    (y : ListNondegenerate.Coloring (V := V) C) (S : Finset V) : Prop :=
  ∀ v : V, v ∈ S → y v ∈ L v

def ListNondegenerate.ListSystemHasCard {V : Type} [Fintype V] {C : ℕ}
    (L : ListNondegenerate.ListSystem (V := V) C) : Prop :=
  ∀ v : V, (L v).card = C

noncomputable def ListNondegenerate.NeighborColors {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ}
    (y : ListNondegenerate.Coloring (V := V) C) (v : V) :
    Finset (ListNondegenerate.Palette (V := V) C) := by
  classical
  exact (ListNondegenerate.Ne (G := G) v).image y

noncomputable def ListNondegenerate.deg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  (ListNondegenerate.Ne (G := G) v).card

def ListNondegenerate.Nondegenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ}
    (y : ListNondegenerate.Coloring (V := V) C) (c p : ℕ) : Prop :=
  ∀ v : V, ListNondegenerate.deg (G := G) v ≥ p →
    ∃ W : Finset V,
      W ⊆ ListNondegenerate.Ne (G := G) v ∧
      c ≤ W.card ∧
      ListNondegenerate.InjOnFinset (V := V) y W

def ListNondegenerate.FNondegenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {C : ℕ}
    (y : ListNondegenerate.Coloring (V := V) C) (f : Finset (ℕ × ℕ)) : Prop :=
  ∀ cp ∈ f, ListNondegenerate.Nondegenerate (G := G) (V := V) (C := C) y cp.1 cp.2

theorem ListNondegenerate.badnessAt_le_of_card_le {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C c : ℕ}
(y y' : ListNondegenerate.Coloring (V := V) C)
(v : V)
(hcard : (ListNondegenerate.NeighborColors (G := G) (y := y) v).card ≤
          (ListNondegenerate.NeighborColors (G := G) (y := y') v).card) :
    ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
      if ListNondegenerate.deg (G := G) v ≥ k then
        k - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card
      else 0)
    ≤
    ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
      if ListNondegenerate.deg (G := G) v ≥ k then
        k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
      else 0) := by
  classical
  -- Let `Ks` be the index finset
  refine Finset.sum_le_sum ?_
  intro k hk
  by_cases hdeg : ListNondegenerate.deg (G := G) v ≥ k
  · -- In this case, both summands are the truncated subtractions.
    simpa [hdeg] using (tsub_le_tsub_left hcard k)
  · -- Otherwise, both sides are zero.
    simp [hdeg]

theorem ListNondegenerate.exists_color_mem_list_not_mem {V : Type} [Fintype V] [DecidableEq V] {C : ℕ}
(L : ListNondegenerate.ListSystem (V := V) C) (u : V)
(hL : ListNondegenerate.ListSystemHasCard (V := V) (C := C) L)
(F : Finset (ListNondegenerate.Palette (V := V) C))
(hF : F.card < C) :
    ∃ a : ListNondegenerate.Palette (V := V) C, a ∈ L u ∧ a ∉ F := by
  classical
  have hcard : F.card < (L u).card := by
    -- rewrite using hL u
    simpa [hL u] using hF
  simpa using (Finset.exists_mem_notMem_of_card_lt_card hcard)

theorem ListNondegenerate.exists_listColoring_properOn {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {D C : ℕ}
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D)
(hC : D + 1 ≤ C)
(L : ListNondegenerate.ListSystem (V := V) C)
(hL : ListNondegenerate.ListSystemHasCard (V := V) (C := C) L) :
    ∀ S : Finset V,
      ∃ y : ListNondegenerate.Coloring (V := V) C,
        ListNondegenerate.IsListColoringOn (V := V) (C := C) L y S ∧
        ListNondegenerate.IsProperOn (G := G) y S := by
  classical
  intro S
  refine Finset.induction_on S ?_ ?_
  · -- base case: S = ∅
    have hCpos : 0 < C := lt_of_lt_of_le (Nat.succ_pos D) hC
    have hLn : ∀ v : V, (L v).Nonempty := by
      intro v
      -- `0 < (L v).card` since `(L v).card = C` and `0 < C`
      have : 0 < (L v).card := by
        simpa [hL v] using hCpos
      exact Finset.card_pos.mp this
    let y : ListNondegenerate.Coloring (V := V) C := fun v => Classical.choose (hLn v)
    refine ⟨y, ?_, ?_⟩
    · intro v hv
      simpa using hv
    · intro u v hu hv hAdj
      simpa using hu
  · -- inductive step
    intro v S hvS ih
    rcases ih with ⟨y0, hy0L, hy0Proper⟩
    let N : Finset V := (ListNondegenerate.Ne (G := G) v).filter (fun u => u ∈ S)
    let forbidden : Finset (ListNondegenerate.Palette (V := V) C) := N.image y0
    have hforbidden_le_D : forbidden.card ≤ D := by
      have h1 : forbidden.card ≤ N.card := by
        simpa [forbidden] using (Finset.card_image_le (f := y0) (s := N))
      have h2 : N.card ≤ ListNondegenerate.deg (G := G) v := by
        have h2' : N.card ≤ (ListNondegenerate.Ne (G := G) v).card := by
          simpa [N] using
            (Finset.card_filter_le (s := ListNondegenerate.Ne (G := G) v) (p := fun u => u ∈ S))
        simpa [ListNondegenerate.deg] using h2'
      have h3 : forbidden.card ≤ ListNondegenerate.deg (G := G) v := le_trans h1 h2
      exact le_trans h3 (hΔ v)
    have hDltC : D < C := lt_of_lt_of_le (Nat.lt_succ_self D) hC
    have hforbidden_lt_L : forbidden.card < (L v).card := by
      have : forbidden.card < C := lt_of_le_of_lt hforbidden_le_D hDltC
      simpa [hL v] using this
    obtain ⟨a, haL, haNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hforbidden_lt_L
    let y : ListNondegenerate.Coloring (V := V) C := fun x => if x = v then a else y0 x
    refine ⟨y, ?_, ?_⟩
    · -- list-coloring property
      intro x hx
      by_cases hxv : x = v
      · subst hxv
        simpa [y] using haL
      · have hxS : x ∈ S := by
          rcases Finset.mem_insert.mp hx with hx | hx
          · exact (hxv hx).elim
          · exact hx
        have : y0 x ∈ L x := hy0L x hxS
        simpa [y, hxv] using this
    · -- properness
      intro u w hu hw hAdj
      by_cases huv : u = v
      · -- u = v
        subst u
        by_cases hwv : w = v
        · -- w = v
          subst w
          exfalso
          exact (G.loopless v) hAdj
        · -- w ≠ v
          have hwS : w ∈ S := by
            rcases Finset.mem_insert.mp hw with hw | hwS
            · exact (hwv hw).elim
            · exact hwS
          have hwN : w ∈ N := by
            have hwNe : w ∈ ListNondegenerate.Ne (G := G) v := by
              simpa [ListNondegenerate.Ne] using hAdj
            simp [N, hwNe, hwS]
          have hy0w_forbidden : y0 w ∈ forbidden := Finset.mem_image_of_mem y0 hwN
          have ha_neq : a ≠ y0 w := by
            intro hEq
            apply haNot
            simpa [hEq] using hy0w_forbidden
          simpa [y, hwv] using ha_neq
      · -- u ≠ v
        have huS : u ∈ S := by
          rcases Finset.mem_insert.mp hu with hu | huS
          · exact (huv hu).elim
          · exact huS
        by_cases hwv : w = v
        · -- w = v
          subst w
          have huN : u ∈ N := by
            have huNe : u ∈ ListNondegenerate.Ne (G := G) v := by
              have : G.Adj v u := G.symm hAdj
              simpa [ListNondegenerate.Ne] using this
            simp [N, huNe, huS]
          have hy0u_forbidden : y0 u ∈ forbidden := Finset.mem_image_of_mem y0 huN
          have ha_neq : a ≠ y0 u := by
            intro hEq
            apply haNot
            simpa [hEq] using hy0u_forbidden
          have : y0 u ≠ a := by
            intro hEq
            exact ha_neq hEq.symm
          simpa [y, huv] using this
        · -- w ≠ v
          have hwS : w ∈ S := by
            rcases Finset.mem_insert.mp hw with hw | hwS
            · exact (hwv hw).elim
            · exact hwS
          have : y0 u ≠ y0 w := hy0Proper huS hwS hAdj
          simpa [y, huv, hwv] using this

theorem ListNondegenerate.exists_proper_list_coloring_of_maxDegree {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {D C : ℕ}
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D)
(hC : D + 1 ≤ C) :
    ∀ (L : ListNondegenerate.ListSystem (V := V) C),
      ListNondegenerate.ListSystemHasCard (V := V) (C := C) L →
      ∃ (y : ListNondegenerate.Coloring (V := V) C),
        ListNondegenerate.IsListColoring (V := V) (C := C) L y ∧
        ListNondegenerate.IsProper (G := G) y := by
  classical
  intro L hL
  obtain ⟨y, hyL, hyP⟩ :=
    ListNondegenerate.exists_listColoring_properOn (G := G) (D := D) (C := C)
      hΔ hC L hL (Finset.univ : Finset V)
  refine ⟨y, ?_, ?_⟩
  · intro v
    exact hyL v (by simp)
  · intro u v huv
    exact hyP (u := u) (v := v) (by simp) (by simp) huv

theorem ListNondegenerate.exists_subset_injOn_of_card_image_ge {α β : Type} [DecidableEq α] [DecidableEq β]
(f : α → β) (s : Finset α) (n : ℕ)
(hn : n ≤ (s.image f).card) :
    ∃ t : Finset α, t ⊆ s ∧ t.card = n ∧ Set.InjOn f (↑t : Set α) := by
  classical
  obtain ⟨u, hu_sub, hu_card⟩ := Finset.exists_subset_card_eq hn
  -- For each `b ∈ u`, choose `a ∈ s` with `f a = b`.
  let g : {b // b ∈ u} → α := fun b =>
    Classical.choose (Finset.mem_image.mp (hu_sub b.2))
  have hg_mem (b : {b // b ∈ u}) : g b ∈ s :=
    (Classical.choose_spec (Finset.mem_image.mp (hu_sub b.2))).1
  have hg_apply (b : {b // b ∈ u}) : f (g b) = b.1 :=
    (Classical.choose_spec (Finset.mem_image.mp (hu_sub b.2))).2
  have hg_inj : Function.Injective g := by
    intro b1 b2 h
    apply Subtype.ext
    have : f (g b1) = f (g b2) := congrArg f h
    simpa [hg_apply] using this
  let t : Finset α := u.attach.image g
  refine ⟨t, ?_, ?_, ?_⟩
  · -- t ⊆ s
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
    exact hg_mem b
  · -- card t = n
    have ht : t.card = u.attach.card := by
      simpa [t] using (Finset.card_image_of_injective (f := g) u.attach hg_inj)
    -- `u.attach.card = u.card`
    simpa [ht, hu_card]
  · -- InjOn
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨ba, hba, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨bb, hbb, rfl⟩
    -- compare the corresponding elements of `u`
    have hval : ba.1 = bb.1 := by
      simpa [hg_apply] using hab
    have hsub : ba = bb := by
      apply Subtype.ext
      exact hval
    -- now rewrite
    simpa [hsub]


theorem ListNondegenerate.exists_two_neighbors_eq_color_of_card_neighborColors_lt {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C)
(v : V) {k : ℕ}
(hk : k ≤ ListNondegenerate.deg (G := G) v)
(hcard : (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < k) :
    ∃ u ∈ ListNondegenerate.Ne (G := G) v,
      ∃ w ∈ ListNondegenerate.Ne (G := G) v,
        u ≠ w ∧ y u = y w := by
  classical
  have hk' : k ≤ (ListNondegenerate.Ne (G := G) v).card := by
    simpa [ListNondegenerate.deg] using hk
  have hcard' : ((ListNondegenerate.Ne (G := G) v).image y).card < k := by
    simpa [ListNondegenerate.NeighborColors] using hcard
  have hlt : ((ListNondegenerate.Ne (G := G) v).image y).card <
      (ListNondegenerate.Ne (G := G) v).card :=
    lt_of_lt_of_le hcard' hk'
  have hnotinj : ¬ Set.InjOn y (↑(ListNondegenerate.Ne (G := G) v) : Set V) := by
    intro hinj
    have hEq : ((ListNondegenerate.Ne (G := G) v).image y).card =
        (ListNondegenerate.Ne (G := G) v).card := by
      simpa using
        (Finset.card_image_of_injOn (s := ListNondegenerate.Ne (G := G) v) (f := y) hinj)
    exact (ne_of_lt hlt) hEq
  have h' : ∃ u, u ∈ (↑(ListNondegenerate.Ne (G := G) v) : Set V) ∧
      ∃ w, w ∈ (↑(ListNondegenerate.Ne (G := G) v) : Set V) ∧ y u = y w ∧ u ≠ w := by
    have h' : ¬ Set.InjOn y (↑(ListNondegenerate.Ne (G := G) v) : Set V) := hnotinj
    -- unfold InjOn so push_neg can see the quantifiers
    simp [Set.InjOn] at h'
    push_neg at h'
    simpa [Set.InjOn] using h'
  rcases h' with ⟨u, hu, w, hw, hEq, hne⟩
  refine ⟨u, ?_, w, ?_, ?_⟩
  · simpa using hu
  · simpa using hw
  · exact ⟨hne, hEq⟩

theorem ListNondegenerate.exists_v_k_of_badness_pos {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C c : ℕ}
(y : ListNondegenerate.Coloring (V := V) C) :
    (Finset.univ.sum (fun v : V =>
      ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
        if ListNondegenerate.deg (G := G) v ≥ k then
          k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
        else 0))) > 0 →
      ∃ v : V, ∃ k : ℕ,
        2 ≤ k ∧ k ≤ c ∧
        ListNondegenerate.deg (G := G) v ≥ k ∧
        (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < k := by
  intro hpos
  classical
  let Ks : Finset ℕ := (Finset.range (c + 1)).filter (fun k => 2 ≤ k)
  have hpos' :
      (Finset.univ.sum (fun v : V =>
        Ks.sum (fun k =>
          if ListNondegenerate.deg (G := G) v ≥ k then
            k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
          else 0))) > 0 := by
    simpa [Ks] using hpos
  have hsum_ne :
      (Finset.univ.sum (fun v : V =>
        Ks.sum (fun k =>
          if ListNondegenerate.deg (G := G) v ≥ k then
            k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
          else 0))) ≠ 0 := by
    exact Nat.ne_of_gt hpos'
  rcases Finset.exists_ne_zero_of_sum_ne_zero hsum_ne with ⟨v, hv, hv_ne⟩
  have hv_ne' :
      Ks.sum (fun k =>
          if ListNondegenerate.deg (G := G) v ≥ k then
            k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
          else 0) ≠ 0 := by
    simpa using hv_ne
  rcases Finset.exists_ne_zero_of_sum_ne_zero hv_ne' with ⟨k, hk, hk_ne⟩
  have hk_range : k ∈ Finset.range (c + 1) := (Finset.mem_filter.mp hk).1
  have hk2 : 2 ≤ k := (Finset.mem_filter.mp hk).2
  have hk_le_c : k ≤ c := by
    have hk_lt : k < c + 1 := Finset.mem_range.mp hk_range
    exact Nat.lt_succ_iff.mp hk_lt
  by_cases hdeg : ListNondegenerate.deg (G := G) v ≥ k
  · have hk_sub_ne :
        k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card ≠ 0 := by
        simpa [hdeg] using hk_ne
    have hk_sub_pos :
        0 < k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card :=
      Nat.pos_of_ne_zero hk_sub_ne
    have hcard_lt :
        (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < k := by
      exact (tsub_pos_iff_lt).1 hk_sub_pos
    exact ⟨v, k, hk2, hk_le_c, hdeg, hcard_lt⟩
  · exfalso
    have :
        (if ListNondegenerate.deg (G := G) v ≥ k then
            k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
          else 0) = 0 := by
      simp [hdeg]
    exact hk_ne this

theorem ListNondegenerate.injOnFinset_iff_setInjOn {V α : Type} (y : V → α) (W : Finset V) :
    ListNondegenerate.InjOnFinset (V := V) y W ↔ Set.InjOn y (↑W : Set V) := by
  classical
  simp [ListNondegenerate.InjOnFinset, Set.InjOn]

theorem ListNondegenerate.card_neighborColors_of_nondegenerate {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C) {c p : ℕ} :
    ListNondegenerate.Nondegenerate (G := G) (V := V) (C := C) y c p →
    ∀ v : V, ListNondegenerate.deg (G := G) v ≥ p →
      c ≤ (ListNondegenerate.NeighborColors (G := G) y v).card := by
  intro hnd
  intro v hvdeg
  classical
  rcases hnd v hvdeg with ⟨W, hWsub, hcW, hInj⟩
  have hSetInj : Set.InjOn y (↑W : Set V) :=
    (ListNondegenerate.injOnFinset_iff_setInjOn (y := y) (W := W)).1 hInj
  have hcard_image : (W.image y).card = W.card := by
    simpa using (Finset.card_image_of_injOn (f := y) (s := W) hSetInj)
  have hc_image : c ≤ (W.image y).card := by
    calc
      c ≤ W.card := hcW
      _ = (W.image y).card := by simpa using hcard_image.symm
  have hsubset : W.image y ⊆ (ListNondegenerate.Ne (G := G) v).image y := by
    exact Finset.image_subset_image hWsub
  have hcard_le : (W.image y).card ≤ (ListNondegenerate.NeighborColors (G := G) y v).card := by
    have : (W.image y).card ≤ ((ListNondegenerate.Ne (G := G) v).image y).card :=
      Finset.card_le_card hsubset
    simpa [ListNondegenerate.NeighborColors] using this
  exact le_trans hc_image hcard_le

instance ListNondegenerate.instFintypePalette {V : Type} [Fintype V] (C : ℕ) :
    Fintype (ListNondegenerate.Palette (V := V) C) := by
  unfold ListNondegenerate.Palette
  infer_instance

instance ListNondegenerate.instFintypeColoring {V : Type} [Fintype V] [DecidableEq V] (C : ℕ) :
    Fintype (ListNondegenerate.Coloring (V := V) C) := by
  unfold ListNondegenerate.Coloring
  infer_instance

theorem ListNondegenerate.mem_Lin_iff (c : ℕ) (cp : ℕ × ℕ) :
    cp ∈ ListNondegenerate.Lin c ↔ ∃ k : ℕ, 2 ≤ k ∧ k ≤ c ∧ cp = (k, k) := by
  classical
  unfold ListNondegenerate.Lin
  constructor
  · intro h
    rcases Finset.mem_image.1 h with ⟨k, hk, rfl⟩
    rcases Finset.mem_filter.1 hk with ⟨hkRange, hk2⟩
    have hkLe : k ≤ c := by
      have hkLt : k < c + 1 := Finset.mem_range.1 hkRange
      exact (Nat.lt_succ_iff.1 hkLt)
    refine ⟨k, hk2, hkLe, rfl⟩
  · rintro ⟨k, hk2, hkLe, rfl⟩
    apply Finset.mem_image.2
    refine ⟨k, ?_, rfl⟩
    apply Finset.mem_filter.2
    refine ⟨?_, hk2⟩
    apply Finset.mem_range.2
    exact Nat.lt_succ_of_le hkLe

theorem ListNondegenerate.nondegenerate_of_card_neighborColors {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C) {c p : ℕ} :
    (∀ v : V, ListNondegenerate.deg (G := G) v ≥ p →
        c ≤ (ListNondegenerate.NeighborColors (G := G) y v).card) →
      ListNondegenerate.Nondegenerate (G := G) (V := V) (C := C) y c p := by
  classical
  intro h
  intro v hvdeg
  have hc : c ≤ (ListNondegenerate.NeighborColors (G := G) y v).card := h v hvdeg
  have hn : c ≤ ((ListNondegenerate.Ne (G := G) v).image y).card := by
    simpa [ListNondegenerate.NeighborColors] using hc
  rcases
      ListNondegenerate.exists_subset_injOn_of_card_image_ge (f := y)
        (s := ListNondegenerate.Ne (G := G) v) (n := c) hn with
    ⟨t, htSub, htCard, htInj⟩
  have htInjFin : ListNondegenerate.InjOnFinset (V := V) y t := by
    exact (ListNondegenerate.injOnFinset_iff_setInjOn (y := y) (W := t)).2 htInj
  refine ⟨t, htSub, ?_⟩
  refine ⟨?_, htInjFin⟩
  simpa [htCard] using (le_rfl c)


theorem ListNondegenerate.nondegenerate_iff_card_neighborColors {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C) {c p : ℕ} :
    ListNondegenerate.Nondegenerate (G := G) (V := V) (C := C) y c p ↔
      (∀ v : V, ListNondegenerate.deg (G := G) v ≥ p →
        c ≤ (ListNondegenerate.NeighborColors (G := G) y v).card) := by
  constructor
  · intro h
    exact ListNondegenerate.card_neighborColors_of_nondegenerate (G := G) (y := y) h
  · intro h
    exact ListNondegenerate.nondegenerate_of_card_neighborColors (G := G) (y := y) h


theorem ListNondegenerate.FNondegenerate_Lin_iff {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C c : ℕ}
(y : ListNondegenerate.Coloring (V := V) C) :
    ListNondegenerate.FNondegenerate (G := G) (V := V) (C := C) y (ListNondegenerate.Lin c) ↔
      ∀ k : ℕ, 2 ≤ k → k ≤ c →
        (∀ v : V, ListNondegenerate.deg (G := G) v ≥ k →
          k ≤ (ListNondegenerate.NeighborColors (G := G) y v).card) := by
  classical
  constructor
  · intro hF k hk2 hkle
    intro v hv
    have hmem : (k, k) ∈ ListNondegenerate.Lin c := by
      -- use the provided characterization of membership in Lin
      refine (ListNondegenerate.mem_Lin_iff c (k, k)).2 ?_
      exact ⟨k, hk2, hkle, rfl⟩
    have hnd : ListNondegenerate.Nondegenerate (G := G) (V := V) (C := C) y k k := by
      -- unfold FNondegenerate and specialize
      simpa [ListNondegenerate.FNondegenerate] using hF (k, k) hmem
    -- translate Nondegenerate into the neighbor-color cardinality condition
    have hineq :=
      (ListNondegenerate.nondegenerate_iff_card_neighborColors (G := G) (y := y)
            (c := k) (p := k)).1 hnd
    exact hineq v hv
  · intro h
    -- unfold FNondegenerate and prove the required Nondegenerate condition for any cp ∈ Lin c
    intro cp hcp
    rcases (ListNondegenerate.mem_Lin_iff c cp).1 hcp with ⟨k, hk2, hkle, rfl⟩
    -- now the goal is Nondegenerate y k k
    refine (ListNondegenerate.nondegenerate_iff_card_neighborColors (G := G) (y := y)
            (c := k) (p := k)).2 ?_
    exact h k hk2 hkle

theorem ListNondegenerate.FNondegenerate_Lin_iff_min {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C c : ℕ}
(y : ListNondegenerate.Coloring (V := V) C) :
    ListNondegenerate.FNondegenerate (G := G) (V := V) (C := C) y (ListNondegenerate.Lin c) ↔
      ∀ v : V,
        2 ≤ ListNondegenerate.deg (G := G) v →
          min c (ListNondegenerate.deg (G := G) v) ≤
            (ListNondegenerate.NeighborColors (G := G) y v).card := by
  classical
  -- unfold `FNondegenerate (Lin c)` via the provided axiom
  rw [ListNondegenerate.FNondegenerate_Lin_iff (G := G) (y := y) (C := C) (c := c)]
  constructor
  · intro h v hvdeg2
    by_cases hdc : ListNondegenerate.deg (G := G) v ≤ c
    ·
      have h' :
          ListNondegenerate.deg (G := G) v ≤
            (ListNondegenerate.NeighborColors (G := G) y v).card :=
        h (ListNondegenerate.deg (G := G) v) hvdeg2 hdc v (le_rfl)
      simpa [min_eq_right hdc] using h'
    ·
      have hcd : c ≤ ListNondegenerate.deg (G := G) v :=
        le_of_lt (lt_of_not_ge hdc)
      by_cases hc2 : 2 ≤ c
      ·
        have h' :
            c ≤ (ListNondegenerate.NeighborColors (G := G) y v).card :=
          h c hc2 (le_rfl) v hcd
        simpa [min_eq_left hcd] using h'
      ·
        -- Here `c < 2`, so `c ≤ 1`. Also `deg v ≥ 2`, hence `NeighborColors` is nonempty.
        have hc1 : c ≤ 1 := by
          have hlt : c < 2 := lt_of_not_ge hc2
          exact (Nat.lt_succ_iff).1 (by simpa using hlt)
        have hne : (ListNondegenerate.Ne (G := G) v).Nonempty := by
          have hv2' : 2 ≤ (ListNondegenerate.Ne (G := G) v).card := by
            simpa [ListNondegenerate.deg] using hvdeg2
          have hpos : 0 < (ListNondegenerate.Ne (G := G) v).card :=
            lt_of_lt_of_le (by decide : 0 < 2) hv2'
          exact (Finset.card_pos).1 hpos
        have hnc : (ListNondegenerate.NeighborColors (G := G) y v).Nonempty := by
          simpa [ListNondegenerate.NeighborColors] using hne.image y
        have hpos_nc : 0 < (ListNondegenerate.NeighborColors (G := G) y v).card :=
          (Finset.card_pos).2 hnc
        have hone : 1 ≤ (ListNondegenerate.NeighborColors (G := G) y v).card :=
          (Nat.succ_le_iff).2 hpos_nc
        have hc_card : c ≤ (ListNondegenerate.NeighborColors (G := G) y v).card :=
          le_trans hc1 hone
        simpa [min_eq_left hcd] using hc_card
  · intro h k hk2 hkc v hvk
    have hv2 : 2 ≤ ListNondegenerate.deg (G := G) v := le_trans hk2 hvk
    have hmin :
        min c (ListNondegenerate.deg (G := G) v) ≤
          (ListNondegenerate.NeighborColors (G := G) y v).card :=
      h v hv2
    have hkmin : k ≤ min c (ListNondegenerate.deg (G := G) v) :=
      le_min hkc hvk
    exact le_trans hkmin hmin

def ListNondegenerate.recolor {V : Type} [Fintype V] [DecidableEq V] {C : ℕ}
    (y : ListNondegenerate.Coloring (V := V) C) (u : V)
    (a : ListNondegenerate.Palette (V := V) C) :
    ListNondegenerate.Coloring (V := V) C :=
  fun x => if x = u then a else y x

theorem ListNondegenerate.card_neighborColors_recolor_ge_sub_one {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C)
(u t : V) (a : ListNondegenerate.Palette (V := V) C) :
    (ListNondegenerate.NeighborColors (G := G)
        (y := ListNondegenerate.recolor (y := y) u a) t).card ≥
      (ListNondegenerate.NeighborColors (G := G) (y := y) t).card - 1 := by
  classical
  by_cases hu : u ∈ ListNondegenerate.Ne (G := G) t
  ·
    have hsubset :
        (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u) ⊆
          ListNondegenerate.NeighborColors (G := G)
            (y := ListNondegenerate.recolor (y := y) u a) t := by
      intro c hc
      have hc' : c ∈ ListNondegenerate.NeighborColors (G := G) (y := y) t :=
          Finset.mem_of_mem_erase hc
      have hne : c ≠ y u := Finset.ne_of_mem_erase hc
      rcases Finset.mem_image.mp hc' with ⟨v, hv, rfl⟩
      have hvneq : v ≠ u := by
        intro hvu
        subst hvu
        exact hne rfl
      refine Finset.mem_image.mpr ?_
      refine ⟨v, hv, ?_⟩
      simp [ListNondegenerate.recolor, hvneq]
    have hcard_erase_le :
        ((ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u)).card ≤
          (ListNondegenerate.NeighborColors (G := G)
            (y := ListNondegenerate.recolor (y := y) u a) t).card :=
      Finset.card_le_card hsubset
    have hpred :
        (ListNondegenerate.NeighborColors (G := G) (y := y) t).card - 1 ≤
          ((ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u)).card := by
      simpa using
        (Finset.pred_card_le_card_erase
          (s := ListNondegenerate.NeighborColors (G := G) (y := y) t) (a := y u))
    exact le_trans hpred hcard_erase_le
  ·
    have hEq :
        ListNondegenerate.NeighborColors (G := G)
            (y := ListNondegenerate.recolor (y := y) u a) t =
          ListNondegenerate.NeighborColors (G := G) (y := y) t := by
      unfold ListNondegenerate.NeighborColors
      apply Finset.image_congr
      intro v hv
      have hvneq : v ≠ u := by
        intro hvu
        subst hvu
        exact hu hv
      simp [ListNondegenerate.recolor, hvneq]
    simpa [hEq] using
      (Nat.sub_le_self
        (ListNondegenerate.NeighborColors (G := G) (y := y) t).card 1)

theorem ListNondegenerate.card_neighborColors_recolor_of_duplicate {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C)
{v u0 u1 : V} (a : ListNondegenerate.Palette (V := V) C)
(hu0 : u0 ∈ ListNondegenerate.Ne (G := G) v)
(hu1 : u1 ∈ ListNondegenerate.Ne (G := G) v)
(hu01 : u0 ≠ u1)
(hcol : y u0 = y u1)
(ha : a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) v) :
    (ListNondegenerate.NeighborColors (G := G)
          (y := ListNondegenerate.recolor (y := y) u0 a) v).card =
      (ListNondegenerate.NeighborColors (G := G) (y := y) v).card + 1 := by
  classical
  -- Let N be the neighbor set of v.
  let N : Finset V := ListNondegenerate.Ne (G := G) v
  have hu0N : u0 ∈ N := hu0
  have hu1N : u1 ∈ N := hu1

  have himage :
      N.image (ListNondegenerate.recolor (y := y) u0 a) = insert a (N.image y) := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_image.1 hc with ⟨w, hwN, rfl⟩
      by_cases hwu : w = u0
      · subst w
        simp [ListNondegenerate.recolor]
      ·
        have hwmem : y w ∈ N.image y :=
          Finset.mem_image.2 ⟨w, hwN, rfl⟩
        have hwmem' : y w ∈ insert a (N.image y) := Finset.mem_insert_of_mem hwmem
        simpa [ListNondegenerate.recolor, hwu] using hwmem'
    · intro hc
      rcases Finset.mem_insert.1 hc with rfl | hc
      ·
        -- show a is in the new image, coming from u0
        exact Finset.mem_image.2 ⟨u0, hu0N, by simp [ListNondegenerate.recolor]⟩
      ·
        rcases Finset.mem_image.1 hc with ⟨w, hwN, rfl⟩
        by_cases hwu : w = u0
        · subst w
          -- the old color y u0 is still present via u1
          refine Finset.mem_image.2 ?_
          refine ⟨u1, hu1N, ?_⟩
          have hu10 : (u1 : V) ≠ u0 := hu01.symm
          simp [ListNondegenerate.recolor, hu10, hcol.symm]
        ·
          refine Finset.mem_image.2 ?_
          refine ⟨w, hwN, ?_⟩
          simp [ListNondegenerate.recolor, hwu]

  have hset :
      ListNondegenerate.NeighborColors (G := G)
          (y := ListNondegenerate.recolor (y := y) u0 a) v
        =
        insert a (ListNondegenerate.NeighborColors (G := G) (y := y) v) := by
    -- unfold the definitions and use `himage`
    simpa [ListNondegenerate.NeighborColors, N, himage]

  -- Now compute the cardinality using `card_insert_of_not_mem`.
  simpa [hset] using (Finset.card_insert_of_not_mem ha)


theorem ListNondegenerate.isListColoring_recolor {V : Type} [Fintype V] [DecidableEq V] {C : ℕ}
(L : ListNondegenerate.ListSystem (V := V) C)
(y : ListNondegenerate.Coloring (V := V) C)
(u : V) (a : ListNondegenerate.Palette (V := V) C) :
    ListNondegenerate.IsListColoring (V := V) (C := C) L y →
    a ∈ L u →
    ListNondegenerate.IsListColoring (V := V) (C := C) L
      (ListNondegenerate.recolor (y := y) u a) := by
  intro hy ha
  intro x
  by_cases hx : x = u
  · subst hx
    -- now goal is: recolor y u a u ∈ L u
    simpa [ListNondegenerate.recolor, ha]
  · -- x ≠ u
    -- recolor agrees with y at x
    have : ListNondegenerate.recolor (y := y) u a x = y x := by
      simp [ListNondegenerate.recolor, hx]
    -- use hy
    simpa [ListNondegenerate.recolor, hx] using hy x

theorem ListNondegenerate.isProper_recolor {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C)
(u : V) (a : ListNondegenerate.Palette (V := V) C) :
    ListNondegenerate.IsProper (G := G) y →
    (∀ w : V, G.Adj u w → a ≠ y w) →
    ListNondegenerate.IsProper (G := G)
      (ListNondegenerate.recolor (y := y) u a) := by
  intro hyproper hneigh
  intro x v hxv
  -- Case split on whether endpoints are the recolored vertex `u`.
  by_cases hx : x = u
  · subst x
    by_cases hv : v = u
    · subst v
      -- No loops in a simple graph.
      exfalso
      exact (G.loopless u) hxv
    · -- Edge from `u` to `v` with `v ≠ u`.
      simpa [ListNondegenerate.recolor, hv] using (hneigh v hxv)
  · by_cases hv : v = u
    · subst v
      -- Use symmetry of adjacency.
      have h := hneigh x (G.symm hxv)
      -- `h : a ≠ y x`, so we can flip it.
      simpa [ListNondegenerate.recolor, hx] using h.symm
    · -- Neither endpoint is `u`, so this reduces to properness of `y`.
      simpa [ListNondegenerate.recolor, hx, hv] using (hyproper hxv)


theorem ListNondegenerate.neighborColors_recolor_eq_insert_erase_of_unique {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
[DecidableEq (ListNondegenerate.Palette (V := V) C)]
(y : ListNondegenerate.Coloring (V := V) C)
{v u0 : V} (a : ListNondegenerate.Palette (V := V) C)
(hu0 : u0 ∈ ListNondegenerate.Ne (G := G) v)
(huniq : ∀ w : V, w ∈ ListNondegenerate.Ne (G := G) v → y w = y u0 → w = u0) :
    ListNondegenerate.NeighborColors (G := G)
        (y := ListNondegenerate.recolor (y := y) u0 a) v =
      insert a ((ListNondegenerate.NeighborColors (G := G) (y := y) v).erase (y u0)) := by
  classical
  ext c
  constructor
  · intro hc
    unfold ListNondegenerate.NeighborColors at hc
    have hc' :
        ∃ w : V,
          w ∈ ListNondegenerate.Ne (G := G) v ∧
            ListNondegenerate.recolor (y := y) u0 a w = c := by
      classical
      letI : DecidableEq (ListNondegenerate.Palette (V := V) C) := Classical.decEq _
      exact Finset.mem_image.mp hc
    rcases hc' with ⟨w, hwNe, hwc⟩
    by_cases hwu : w = u0
    · subst w
      have hcEq : c = a := by
        have : a = c := by
          simpa [ListNondegenerate.recolor] using hwc
        exact this.symm
      subst c
      -- goal has `recolor ... u0` on the left; simplify it
      simpa [ListNondegenerate.recolor] using
        (Finset.mem_insert_self a
          ((ListNondegenerate.NeighborColors (G := G) (y := y) v).erase (y u0)))
    ·
      have hywc : y w = c := by
        simpa [ListNondegenerate.recolor, hwu] using hwc
      have hcne : c ≠ y u0 := by
        intro hcEq
        have hEq : y w = y u0 := hywc.trans hcEq
        exact hwu (huniq w hwNe hEq)
      have hcNC : c ∈ ListNondegenerate.NeighborColors (G := G) (y := y) v := by
        classical
        letI : DecidableEq (ListNondegenerate.Palette (V := V) C) := Classical.decEq _
        unfold ListNondegenerate.NeighborColors
        exact Finset.mem_image.mpr ⟨w, hwNe, hywc⟩
      have hcErase :
          c ∈ (ListNondegenerate.NeighborColors (G := G) (y := y) v).erase (y u0) := by
        exact Finset.mem_erase.mpr ⟨hcne, hcNC⟩
      exact Finset.mem_insert_of_mem hcErase
  · intro hc
    rcases Finset.mem_insert.mp hc with hcEq | hcInErase
    · subst c
      classical
      letI : DecidableEq (ListNondegenerate.Palette (V := V) C) := Classical.decEq _
      unfold ListNondegenerate.NeighborColors
      refine Finset.mem_image.mpr ?_
      refine ⟨u0, hu0, ?_⟩
      simp [ListNondegenerate.recolor]
    ·
      have hcne : c ≠ y u0 := (Finset.mem_erase.mp hcInErase).1
      have hcNC : c ∈ ListNondegenerate.NeighborColors (G := G) (y := y) v :=
        (Finset.mem_erase.mp hcInErase).2
      unfold ListNondegenerate.NeighborColors at hcNC
      have hc_w : ∃ w : V, w ∈ ListNondegenerate.Ne (G := G) v ∧ y w = c := by
        classical
        letI : DecidableEq (ListNondegenerate.Palette (V := V) C) := Classical.decEq _
        exact Finset.mem_image.mp hcNC
      rcases hc_w with ⟨w, hwNe, hyw⟩
      classical
      letI : DecidableEq (ListNondegenerate.Palette (V := V) C) := Classical.decEq _
      unfold ListNondegenerate.NeighborColors
      refine Finset.mem_image.mpr ?_
      refine ⟨w, hwNe, ?_⟩
      by_cases hwu : w = u0
      · subst w
        exfalso
        exact hcne hyw.symm
      ·
        simpa [ListNondegenerate.recolor, hwu] using hyw

theorem ListNondegenerate.card_neighborColors_recolor_of_unique {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
[DecidableEq (ListNondegenerate.Palette (V := V) C)]
(y : ListNondegenerate.Coloring (V := V) C)
{v u0 : V} (a : ListNondegenerate.Palette (V := V) C)
(hu0 : u0 ∈ ListNondegenerate.Ne (G := G) v)
(huniq : ∀ w : V, w ∈ ListNondegenerate.Ne (G := G) v → y w = y u0 → w = u0)
(ha : a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) v) :
    (ListNondegenerate.NeighborColors (G := G)
          (y := ListNondegenerate.recolor (y := y) u0 a) v).card =
      (ListNondegenerate.NeighborColors (G := G) (y := y) v).card := by
  classical
  -- abbreviate the original neighbor-color set
  let S : Finset (ListNondegenerate.Palette (V := V) C) :=
    ListNondegenerate.NeighborColors (G := G) (y := y) v

  have hyu0 : y u0 ∈ S := by
    -- `hu0` witnesses that `u0` is a neighbor of `v`
    -- hence its color appears in the image defining `NeighborColors`
    simpa [S, ListNondegenerate.NeighborColors] using
      (Finset.mem_image.2 ⟨u0, hu0, rfl⟩)

  have haErase : a ∉ S.erase (y u0) := by
    intro ha'
    have haS : a ∈ S := (Finset.mem_erase.mp ha').2
    exact ha haS

  have hle : 1 ≤ S.card := by
    have hpos : 0 < S.card :=
      Finset.card_pos.mpr ⟨y u0, hyu0⟩
    exact (Nat.succ_le_iff.2 hpos)

  have hcard : (insert a (S.erase (y u0))).card = S.card := by
    calc
      (insert a (S.erase (y u0))).card = (S.erase (y u0)).card + 1 := by
        exact Finset.card_insert_of_not_mem haErase
      _ = (S.card - 1) + 1 := by
        simp [Finset.card_erase_of_mem hyu0]
      _ = S.card := by
        simpa using Nat.sub_add_cancel hle

  -- rewrite neighbor colors after recoloring using the supplied axiom
  have hEq' :
      ListNondegenerate.NeighborColors (G := G)
          (y := ListNondegenerate.recolor (y := y) u0 a) v =
        insert a (S.erase (y u0)) := by
    simpa [S] using
      ListNondegenerate.neighborColors_recolor_eq_insert_erase_of_unique
        (G := G) (y := y) (v := v) (u0 := u0) (a := a) hu0 huniq

  -- finish by rewriting the goal and applying `hcard`
  simpa [S, hEq'] using hcard

theorem ListNondegenerate.neighborColors_recolor_eq_insert_of_duplicate {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
[DecidableEq (ListNondegenerate.Palette (V := V) C)]
(y : ListNondegenerate.Coloring (V := V) C)
{v u0 u1 : V} (a : ListNondegenerate.Palette (V := V) C)
(hu0 : u0 ∈ ListNondegenerate.Ne (G := G) v)
(hu1 : u1 ∈ ListNondegenerate.Ne (G := G) v)
(hu01 : u0 ≠ u1)
(hcol : y u0 = y u1) :
    ListNondegenerate.NeighborColors (G := G)
        (y := ListNondegenerate.recolor (y := y) u0 a) v =
      insert a (ListNondegenerate.NeighborColors (G := G) (y := y) v) := by
  classical
  let N : Finset V := ListNondegenerate.Ne (G := G) v
  have hu0N : u0 ∈ N := hu0
  have hu1N : u1 ∈ N := hu1

  have hNC (y' : ListNondegenerate.Coloring (V := V) C) :
      ListNondegenerate.NeighborColors (G := G) (y := y') v = N.image y' := by
    ext c
    simp [ListNondegenerate.NeighborColors, N]

  have himage : N.image (ListNondegenerate.recolor (y := y) u0 a) =
      insert a (N.image y) := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_image.1 hc with ⟨w, hwN, rfl⟩
      by_cases hwu : w = u0
      · subst w
        simp [ListNondegenerate.recolor]
      ·
        have : y w ∈ N.image y := Finset.mem_image.2 ⟨w, hwN, rfl⟩
        simpa [ListNondegenerate.recolor, hwu] using (Finset.mem_insert_of_mem this)
    · intro hc
      rcases Finset.mem_insert.1 hc with hc | hc
      · subst hc
        exact Finset.mem_image.2 ⟨u0, hu0N, by simp [ListNondegenerate.recolor]⟩
      ·
        rcases Finset.mem_image.1 hc with ⟨w, hwN, rfl⟩
        by_cases hwu : w = u0
        · subst w
          refine Finset.mem_image.2 ⟨u1, hu1N, ?_⟩
          have hu10 : (u1 : V) ≠ u0 := hu01.symm
          simp [ListNondegenerate.recolor, hu10, hcol.symm]
        ·
          refine Finset.mem_image.2 ⟨w, hwN, ?_⟩
          simp [ListNondegenerate.recolor, hwu]

  have hNCy : ListNondegenerate.NeighborColors (G := G) (y := y) v = N.image y := hNC (y' := y)

  calc
    ListNondegenerate.NeighborColors (G := G)
        (y := ListNondegenerate.recolor (y := y) u0 a) v
        = N.image (ListNondegenerate.recolor (y := y) u0 a) := by
            simpa using hNC (y' := ListNondegenerate.recolor (y := y) u0 a)
    _ = insert a (N.image y) := himage
    _ = insert a (ListNondegenerate.NeighborColors (G := G) (y := y) v) := by
          simpa using congrArg (fun s => insert a s) hNCy.symm

theorem ListNondegenerate.neighborColors_recolor_eq_of_not_mem {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {C : ℕ}
(y : ListNondegenerate.Coloring (V := V) C)
(u v : V) (a : ListNondegenerate.Palette (V := V) C)
(hu : u ∉ ListNondegenerate.Ne (G := G) v) :
    ListNondegenerate.NeighborColors (G := G)
        (y := ListNondegenerate.recolor (y := y) u a) v =
      ListNondegenerate.NeighborColors (G := G) (y := y) v := by
  classical
  unfold ListNondegenerate.NeighborColors
  refine Finset.image_congr ?_
  intro w hw
  have hwu : w ≠ u := by
    intro h
    apply hu
    -- show u ∈ Ne v
    simpa [h] using hw
  simp [ListNondegenerate.recolor, hwu]

theorem ListNondegenerate.exists_color_for_recolor_from_duplicate_aux_card_le_c {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {D C c : ℕ} (hc : 2 ≤ c)
(hC : C = max (D + c * c - 1) ((D + 1) * c))
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D)
(L : ListNondegenerate.ListSystem (V := V) C)
(hL : ListNondegenerate.ListSystemHasCard (V := V) (C := C) L)
(y : ListNondegenerate.Coloring (V := V) C)
(hyL : ListNondegenerate.IsListColoring (V := V) (C := C) L y)
(hyP : ListNondegenerate.IsProper (G := G) y)
{v u0 u1 : V} {k : ℕ}
(hk2 : 2 ≤ k) (hk_le_c : k ≤ c)
(hk_le : k ≤ ListNondegenerate.deg (G := G) v)
(hcard_lt : (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < k)
(hu0 : u0 ∈ ListNondegenerate.Ne (G := G) v)
(hu1 : u1 ∈ ListNondegenerate.Ne (G := G) v)
(hu01 : u0 ≠ u1)
(hcol : y u0 = y u1) :
    ∃ (u : V), (u = u0 ∨ u = u1) ∧
      ∃ a : ListNondegenerate.Palette (V := V) C,
        a ∈ L u ∧
        a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) v ∧
        a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) u ∧
        (∀ t : V,
          (ListNondegenerate.NeighborColors (G := G)
              (y := ListNondegenerate.recolor (y := y) u a) t).card ≥
            (ListNondegenerate.NeighborColors (G := G) (y := y) t).card ∨
          c < (ListNondegenerate.NeighborColors (G := G) (y := y) t).card) := by
  classical
  -- We follow the counting/forbidden-set plan from the informal proof.
  refine ⟨u0, ?_, ?_⟩
  · exact Or.inl rfl
  ·
    -- Define the set of potentially affected vertices (with small neighbor-color sets)
    let u : V := u0
    let T : Finset V :=
      (ListNondegenerate.Ne (G := G) u).filter
        (fun t =>
          (ListNondegenerate.NeighborColors (G := G) (y := y) t).card ≤ c)
    -- Forbidden colors: those used around `v`, around `u`, and (for `t ∈ T`) those used around `t`
    -- except possibly the old color `y u`.
    let F : Finset (ListNondegenerate.Palette (V := V) C) :=
      ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
        ListNondegenerate.NeighborColors (G := G) (y := y) u ∪
          T.biUnion
            (fun t =>
              (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u))

    -- First show that `F` is small enough to apply the list lemma.
    have hc1 : 1 ≤ c := le_trans (by decide : 1 ≤ 2) hc

    have hcard_v_le :
        (ListNondegenerate.NeighborColors (G := G) (y := y) v).card ≤ c - 1 := by
      have hlt_c :
          (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < c :=
        lt_of_lt_of_le hcard_lt hk_le_c
      have hlt' :
          (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < (c - 1).succ := by
        -- rewrite `c` as `(c-1)+1`
        have hc_eq : (c - 1) + 1 = c := Nat.sub_add_cancel hc1
        have :
            (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < (c - 1) + 1 := by
          simpa [hc_eq] using hlt_c
        simpa [Nat.succ_eq_add_one] using this
      exact (Nat.lt_succ_iff).1 hlt'

    have hcard_u_le_D :
        (ListNondegenerate.NeighborColors (G := G) (y := y) u).card ≤ D := by
      -- image-card ≤ source-card
      have hle_deg :
          (ListNondegenerate.NeighborColors (G := G) (y := y) u).card ≤
            (ListNondegenerate.Ne (G := G) u).card := by
        -- unfold NeighborColors
        simpa [ListNondegenerate.NeighborColors] using
          (Finset.card_image_le (s := ListNondegenerate.Ne (G := G) u) (f := y))
      -- and the degree bound
      have hdeg_le : (ListNondegenerate.Ne (G := G) u).card ≤ D := by
        simpa [ListNondegenerate.deg] using hΔ u
      exact le_trans hle_deg hdeg_le

    have hcard_biUnion_le :
        (T.biUnion
              (fun t =>
                (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u))).card ≤
          D * (c - 1) := by
      -- First: card biUnion ≤ card T * (c-1).
      have hT_pointwise :
          ∀ t ∈ T,
            ((ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u)).card ≤ c - 1 := by
        intro t ht
        have htNe : t ∈ ListNondegenerate.Ne (G := G) u :=
          (Finset.mem_filter.1 ht).1
        have htcard :
            (ListNondegenerate.NeighborColors (G := G) (y := y) t).card ≤ c :=
          (Finset.mem_filter.1 ht).2
        -- `u` is a neighbor of `t` by symmetry
        have huNe : u ∈ ListNondegenerate.Ne (G := G) t := by
          have hadj : G.Adj u t := by
            simpa [ListNondegenerate.Ne] using htNe
          have hadj' : G.Adj t u := G.adj_symm hadj
          simpa [ListNondegenerate.Ne, hadj']
        have hyu_mem : y u ∈ ListNondegenerate.NeighborColors (G := G) (y := y) t := by
          -- membership in image
          simpa [ListNondegenerate.NeighborColors] using
            (Finset.mem_image_of_mem y huNe)
        -- erase reduces card by 1
        have hEq :
            ((ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u)).card =
              (ListNondegenerate.NeighborColors (G := G) (y := y) t).card - 1 := by
          simpa using (Finset.card_erase_of_mem hyu_mem)
        have hsub :
            (ListNondegenerate.NeighborColors (G := G) (y := y) t).card - 1 ≤ c - 1 :=
          Nat.sub_le_sub_right htcard 1
        simpa [hEq] using hsub

      have hbi :
          (T.biUnion
                (fun t =>
                  (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u))).card ≤
            T.card * (c - 1) := by
        -- use `card_biUnion_le_card_mul`
        simpa using
          (Finset.card_biUnion_le_card_mul T
            (fun t =>
              (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u)) (c - 1)
            hT_pointwise)

      -- Next: `T.card ≤ deg u ≤ D`.
      have hT_le_deg : T.card ≤ (ListNondegenerate.Ne (G := G) u).card := by
        apply Finset.card_le_card
        intro t ht
        exact (Finset.mem_filter.1 ht).1
      have hdeg_le_D : (ListNondegenerate.Ne (G := G) u).card ≤ D := by
        simpa [ListNondegenerate.deg] using hΔ u

      have hT_le_D : T.card ≤ D := le_trans hT_le_deg hdeg_le_D

      -- combine
      have : T.card * (c - 1) ≤ D * (c - 1) := Nat.mul_le_mul_right (c - 1) hT_le_D
      exact le_trans hbi this

    -- Now bound the whole forbidden set
    have hF_le : F.card ≤ (c - 1) + D + D * (c - 1) := by
      -- F = A ∪ B ∪ C
      have h1 :
          F.card ≤
            (ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
                ListNondegenerate.NeighborColors (G := G) (y := y) u).card +
              (T.biUnion
                    (fun t =>
                      (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u))).card := by
        -- `card_union_le`
        simpa [F] using
          (Finset.card_union_le
            (ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
                ListNondegenerate.NeighborColors (G := G) (y := y) u)
            (T.biUnion
                (fun t =>
                  (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u))))

      have h2 :
          (ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
                ListNondegenerate.NeighborColors (G := G) (y := y) u).card ≤
            (ListNondegenerate.NeighborColors (G := G) (y := y) v).card +
              (ListNondegenerate.NeighborColors (G := G) (y := y) u).card := by
        simpa using
          (Finset.card_union_le
            (ListNondegenerate.NeighborColors (G := G) (y := y) v)
            (ListNondegenerate.NeighborColors (G := G) (y := y) u))

      have hAB :
          (ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
                ListNondegenerate.NeighborColors (G := G) (y := y) u).card ≤
            (c - 1) + D := by
        have hsum :
            (ListNondegenerate.NeighborColors (G := G) (y := y) v).card +
                (ListNondegenerate.NeighborColors (G := G) (y := y) u).card ≤
              (c - 1) + D :=
          add_le_add hcard_v_le hcard_u_le_D
        exact le_trans h2 hsum

      have hC :
          (T.biUnion
                (fun t =>
                  (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u))).card ≤
            D * (c - 1) := hcard_biUnion_le

      -- combine bounds
      have : F.card ≤ ((c - 1) + D) + D * (c - 1) := by
        have := add_le_add hAB hC
        exact le_trans h1 this
      -- tidy up
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

    have hF_lt_mul : F.card < (D + 1) * c := by
      have hbound_lt : (c - 1) + D + D * (c - 1) < (D + 1) * c := by
        -- rewrite the bound as `D + (D+1)*(c-1)` and compare using `D < D+1`.
        have hD : D < D + 1 := Nat.lt_succ_self D
        have hstep : D + (D + 1) * (c - 1) < (D + 1) + (D + 1) * (c - 1) :=
          Nat.add_lt_add_right hD ((D + 1) * (c - 1))
        have hstep' : D + (D + 1) * (c - 1) < (D + 1) * (c - 1) + (D + 1) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
        have hEqL : (c - 1) + D + D * (c - 1) = D + (D + 1) * (c - 1) := by
          have hmul : (D + 1) * (c - 1) = D * (c - 1) + (c - 1) := by
            simpa [Nat.add_mul, Nat.one_mul] using (Nat.add_mul D 1 (c - 1))
          calc
            (c - 1) + D + D * (c - 1)
                = D + (D * (c - 1) + (c - 1)) := by
                    ac_rfl
            _ = D + (D + 1) * (c - 1) := by
                    simp [hmul]
        have hEqR : (D + 1) * (c - 1) + (D + 1) = (D + 1) * c := by
          have hc_eq : (c - 1) + 1 = c := Nat.sub_add_cancel hc1
          calc
            (D + 1) * (c - 1) + (D + 1)
                = (D + 1) * ((c - 1) + 1) := by
                    simpa [Nat.mul_add, Nat.mul_one] using
                      (Nat.mul_add (D + 1) (c - 1) 1).symm
            _ = (D + 1) * c := by simpa [hc_eq]
        simpa [hEqL, hEqR] using hstep'
      exact lt_of_le_of_lt hF_le hbound_lt

    have hmul_le_C : (D + 1) * c ≤ C := by
      -- since `C` is the max of two things
      simpa [hC] using (le_max_right (D + c * c - 1) ((D + 1) * c))

    have hF_lt_C : F.card < C := lt_of_lt_of_le hF_lt_mul hmul_le_C

    -- Pick a color `a` in `L u` avoiding `F`.
    obtain ⟨a, haLu, haF⟩ :=
      ListNondegenerate.exists_color_mem_list_not_mem (V := V) (L := L) (u := u) hL F hF_lt_C

    refine ⟨a, haLu, ?_, ?_, ?_⟩
    · -- a ∉ NeighborColors v
      have : a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) v := by
        intro ha
        have haFmem : a ∈ F := by
          -- membership in the left-most union component
          have : a ∈
              ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
                ListNondegenerate.NeighborColors (G := G) (y := y) u :=
            Finset.mem_union_left _ ha
          exact Finset.mem_union_left _ this
        exact haF haFmem
      exact this
    · -- a ∉ NeighborColors u
      have : a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) u := by
        intro ha
        have haFmem : a ∈ F := by
          have : a ∈
              ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
                ListNondegenerate.NeighborColors (G := G) (y := y) u :=
            Finset.mem_union_right _ ha
          exact Finset.mem_union_left _ this
        exact haF haFmem
      exact this
    · -- The ∀t disjunction
      intro t
      by_cases hct : c < (ListNondegenerate.NeighborColors (G := G) (y := y) t).card
      · exact Or.inr hct
      · -- now card ≤ c
        have hct' : (ListNondegenerate.NeighborColors (G := G) (y := y) t).card ≤ c :=
          le_of_not_gt hct
        -- split depending on whether recoloring vertex `u` is adjacent to `t`.
        by_cases hut : u ∈ ListNondegenerate.Ne (G := G) t
        · -- `u` is adjacent to `t`.
          -- First obtain `a ≠ y u` from `a ∉ NeighborColors v` and `u ∈ Ne v`.
          have ha_not_v : a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) v := by
            intro ha
            have haFmem : a ∈ F := by
              have : a ∈
                  ListNondegenerate.NeighborColors (G := G) (y := y) v ∪
                    ListNondegenerate.NeighborColors (G := G) (y := y) u :=
                Finset.mem_union_left _ ha
              exact Finset.mem_union_left _ this
            exact haF haFmem
          have hyu_mem_v : y u ∈ ListNondegenerate.NeighborColors (G := G) (y := y) v := by
            have huNe_v : u ∈ ListNondegenerate.Ne (G := G) v := by
              simpa [u] using hu0
            simpa [ListNondegenerate.NeighborColors] using
              (Finset.mem_image_of_mem y huNe_v)
          have hau_ne : a ≠ y u := by
            intro hEq
            have ha_mem_v : a ∈ ListNondegenerate.NeighborColors (G := G) (y := y) v := by
              simpa [hEq] using hyu_mem_v
            exact ha_not_v ha_mem_v

          -- Show `t ∈ T` (since `u ∈ Ne t` and `card ≤ c`).
          have htT : t ∈ T := by
            -- `t ∈ Ne u` by symmetry
            have htNe_u : t ∈ ListNondegenerate.Ne (G := G) u := by
              have hadj : G.Adj t u := by
                simpa [ListNondegenerate.Ne] using hut
              have hadj' : G.Adj u t := G.adj_symm hadj
              simpa [ListNondegenerate.Ne, hadj']
            exact Finset.mem_filter.2 ⟨htNe_u, hct'⟩

          -- Extract: `a ∉ (NeighborColors t).erase (y u)` from `a ∉ F`.
          have ha_erase :
              a ∉ (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u) := by
            intro ha
            have : a ∈
                T.biUnion
                  (fun t =>
                    (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u)) := by
              exact (Finset.mem_biUnion.2 ⟨t, htT, ha⟩)
            have : a ∈ F := by
              -- right-most union component
              exact Finset.mem_union_right _ this
            exact haF this

          -- Thus `a ∉ NeighborColors t` (using `a ≠ y u`).
          have ha_not_t : a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) t := by
            intro hat
            have ha_mem_erase :
                a ∈ (ListNondegenerate.NeighborColors (G := G) (y := y) t).erase (y u) :=
              Finset.mem_erase_of_ne_of_mem hau_ne hat
            exact ha_erase ha_mem_erase

          -- Now split on uniqueness of the old color `y u` in the neighborhood of `t`.
          by_cases huniq :
              ∀ w : V,
                w ∈ ListNondegenerate.Ne (G := G) t → y w = y u → w = u
          · -- unique: card stays the same
            have hcardEq :
                (ListNondegenerate.NeighborColors (G := G)
                        (y := ListNondegenerate.recolor (y := y) u a) t).card =
                  (ListNondegenerate.NeighborColors (G := G) (y := y) t).card := by
              -- use the provided axiom
              simpa using
                (ListNondegenerate.card_neighborColors_recolor_of_unique (V := V) (G := G)
                    (y := y) (v := t) (u0 := u) (a := a) hut huniq ha_not_t)
            exact Or.inl (le_of_eq hcardEq.symm)
          · -- not unique: there exists a duplicate neighbor color; then card can only go up.
            have hdup :
                ∃ w : V,
                  w ∈ ListNondegenerate.Ne (G := G) t ∧ y w = y u ∧ w ≠ u := by
              push_neg at huniq
              exact huniq
            rcases hdup with ⟨w, hwNe, hwy, hwu⟩
            have huw : u ≠ w := by
              intro h
              exact hwu h.symm
            have hEq :
                ListNondegenerate.NeighborColors (G := G)
                      (y := ListNondegenerate.recolor (y := y) u a) t =
                  insert a (ListNondegenerate.NeighborColors (G := G) (y := y) t) := by
              -- apply the duplicate axiom
              simpa using
                (ListNondegenerate.neighborColors_recolor_eq_insert_of_duplicate (V := V) (G := G)
                    (y := y) (v := t) (u0 := u) (u1 := w) (a := a) hut hwNe huw hwy.symm)

            have hsub :
                ListNondegenerate.NeighborColors (G := G) (y := y) t ⊆
                  insert a (ListNondegenerate.NeighborColors (G := G) (y := y) t) := by
              intro x hx
              exact Finset.mem_insert_of_mem hx
            have hcard_le :
                (ListNondegenerate.NeighborColors (G := G) (y := y) t).card ≤
                  (insert a (ListNondegenerate.NeighborColors (G := G) (y := y) t)).card :=
              Finset.card_le_card hsub
            have hcard_ge :
                (ListNondegenerate.NeighborColors (G := G) (y := y) t).card ≤
                  (ListNondegenerate.NeighborColors (G := G)
                        (y := ListNondegenerate.recolor (y := y) u a) t).card := by
              simpa [hEq] using hcard_le
            exact Or.inl hcard_ge

        · -- `u` is not adjacent to `t`, so neighbor colors are unchanged.
          have hEq :
              ListNondegenerate.NeighborColors (G := G)
                    (y := ListNondegenerate.recolor (y := y) u a) t =
                ListNondegenerate.NeighborColors (G := G) (y := y) t := by
            simpa using
              (ListNondegenerate.neighborColors_recolor_eq_of_not_mem (V := V) (G := G)
                (y := y) (u := u) (v := t) (a := a) hut)
          have hcardEq :
              (ListNondegenerate.NeighborColors (G := G)
                      (y := ListNondegenerate.recolor (y := y) u a) t).card =
                (ListNondegenerate.NeighborColors (G := G) (y := y) t).card := by
            simpa [hEq]
          exact Or.inl (le_of_eq hcardEq.symm)


theorem ListNondegenerate.exists_color_for_recolor_from_duplicate_aux_badness {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {D C c : ℕ} (hc : 2 ≤ c)
(hC : C = max (D + c * c - 1) ((D + 1) * c))
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D)
(L : ListNondegenerate.ListSystem (V := V) C)
(hL : ListNondegenerate.ListSystemHasCard (V := V) (C := C) L)
(y : ListNondegenerate.Coloring (V := V) C)
(hyL : ListNondegenerate.IsListColoring (V := V) (C := C) L y)
(hyP : ListNondegenerate.IsProper (G := G) y)
{v u0 u1 : V} {k : ℕ}
(hk2 : 2 ≤ k) (hk_le_c : k ≤ c)
(hk_le : k ≤ ListNondegenerate.deg (G := G) v)
(hcard_lt : (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < k)
(hu0 : u0 ∈ ListNondegenerate.Ne (G := G) v)
(hu1 : u1 ∈ ListNondegenerate.Ne (G := G) v)
(hu01 : u0 ≠ u1)
(hcol : y u0 = y u1) :
    ∃ (u : V), (u = u0 ∨ u = u1) ∧
      ∃ a : ListNondegenerate.Palette (V := V) C,
        a ∈ L u ∧
        a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) v ∧
        a ∉ ListNondegenerate.NeighborColors (G := G) (y := y) u ∧
        (∀ t : V,
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
            if ListNondegenerate.deg (G := G) t ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G)
                  (y := ListNondegenerate.recolor (y := y) u a) t).card
            else 0)
          ≤
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
            if ListNondegenerate.deg (G := G) t ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G) (y := y) t).card
            else 0)) := by
  classical
  rcases
      ListNondegenerate.exists_color_for_recolor_from_duplicate_aux_card_le_c
        (G := G) (D := D) (C := C) (c := c) hc hC hΔ L hL y hyL hyP (v := v) (u0 := u0)
        (u1 := u1) (k := k) hk2 hk_le_c hk_le hcard_lt hu0 hu1 hu01 hcol with
    ⟨u, hu, ha⟩
  rcases ha with ⟨a, haLu, hav, hau, hcard_or⟩
  refine ⟨u, hu, ?_⟩
  refine ⟨a, haLu, hav, hau, ?_⟩
  intro t
  cases hcard_or t with
  | inl hge =>
      -- monotonicity of badness when neighbor color set grows
      simpa using
        (ListNondegenerate.badnessAt_le_of_card_le (G := G) (c := c) (y := y)
          (y' := ListNondegenerate.recolor (y := y) u a) (v := t) hge)
  | inr hlt =>
      -- if there are already more than `c` neighbor colors, then both badness sums are zero
      have hafter_ge :
          (ListNondegenerate.NeighborColors (G := G)
                (y := ListNondegenerate.recolor (y := y) u a) t).card ≥
            (ListNondegenerate.NeighborColors (G := G) (y := y) t).card - 1 :=
        ListNondegenerate.card_neighborColors_recolor_ge_sub_one (G := G) (y := y) (u := u) (t := t)
          (a := a)

      have hc_le_pred :
          c ≤ (ListNondegenerate.NeighborColors (G := G) (y := y) t).card - 1 := by
        exact Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlt)

      have hc_le_after :
          c ≤
            (ListNondegenerate.NeighborColors (G := G)
                  (y := ListNondegenerate.recolor (y := y) u a) t).card :=
        le_trans hc_le_pred hafter_ge

      have hsum_after :
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
              if ListNondegenerate.deg (G := G) t ≥ k then
                k -
                    (ListNondegenerate.NeighborColors (G := G)
                        (y := ListNondegenerate.recolor (y := y) u a) t).card
              else 0) =
            0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        have hk_range : k < c + 1 := by
          have hk_mem : k ∈ Finset.range (c + 1) := (Finset.mem_filter.mp hk).1
          exact Finset.mem_range.mp hk_mem
        have hk_le_c : k ≤ c := Nat.lt_succ_iff.mp hk_range
        have hk_le_after :
            k ≤
              (ListNondegenerate.NeighborColors (G := G)
                    (y := ListNondegenerate.recolor (y := y) u a) t).card :=
          le_trans hk_le_c hc_le_after
        have hsub :
            k -
                (ListNondegenerate.NeighborColors (G := G)
                    (y := ListNondegenerate.recolor (y := y) u a) t).card =
              0 :=
          Nat.sub_eq_zero_of_le hk_le_after
        by_cases hdeg : ListNondegenerate.deg (G := G) t ≥ k
        · simp [hdeg, hsub]
        · simp [hdeg]

      have hsum_before :
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
              if ListNondegenerate.deg (G := G) t ≥ k then
                k - (ListNondegenerate.NeighborColors (G := G) (y := y) t).card
              else 0) =
            0 := by
        refine Finset.sum_eq_zero ?_
        intro k hk
        have hk_range : k < c + 1 := by
          have hk_mem : k ∈ Finset.range (c + 1) := (Finset.mem_filter.mp hk).1
          exact Finset.mem_range.mp hk_mem
        have hk_le_c : k ≤ c := Nat.lt_succ_iff.mp hk_range
        have hk_le_before : k ≤ (ListNondegenerate.NeighborColors (G := G) (y := y) t).card := by
          exact le_trans hk_le_c (Nat.le_of_lt hlt)
        have hsub :
            k - (ListNondegenerate.NeighborColors (G := G) (y := y) t).card = 0 :=
          Nat.sub_eq_zero_of_le hk_le_before
        by_cases hdeg : ListNondegenerate.deg (G := G) t ≥ k
        · simp [hdeg, hsub]
        · simp [hdeg]

      -- conclude
      simpa [hsum_after, hsum_before]


theorem ListNondegenerate.neighborColors_recolor_subset_insert {V : Type} [Fintype V] [DecidableEq V] {C : ℕ}
[DecidableEq (ListNondegenerate.Palette (V := V) C)]
(G : SimpleGraph V)
(y : ListNondegenerate.Coloring (V := V) C)
(u v : V) (a : ListNondegenerate.Palette (V := V) C) :
    ListNondegenerate.NeighborColors (G := G)
        (y := ListNondegenerate.recolor (y := y) u a) v ⊆
      insert a (ListNondegenerate.NeighborColors (G := G) (y := y) v) := by
  classical
  intro c hc
  rcases (by
    simpa [ListNondegenerate.NeighborColors] using hc
  ) with ⟨w, hw, rfl⟩
  by_cases hwu : w = u
  · subst hwu
    simp [ListNondegenerate.recolor]
  ·
    have hyw : y w ∈ ListNondegenerate.NeighborColors (G := G) (y := y) v := by
      simpa [ListNondegenerate.NeighborColors] using (Finset.mem_image_of_mem y hw)
    -- recolor does not change w in this case, so the color is already in NeighborColors
    simpa [ListNondegenerate.recolor, hwu] using (Finset.mem_insert_of_mem hyw)


theorem ListNondegenerate.recolor_from_duplicate {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {D C c : ℕ} (hc : 2 ≤ c)
(hC : C = max (D + c * c - 1) ((D + 1) * c))
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D)
(L : ListNondegenerate.ListSystem (V := V) C)
(hL : ListNondegenerate.ListSystemHasCard (V := V) (C := C) L)
(y : ListNondegenerate.Coloring (V := V) C)
(hyL : ListNondegenerate.IsListColoring (V := V) (C := C) L y)
(hyP : ListNondegenerate.IsProper (G := G) y)
{v u0 u1 : V} {k : ℕ}
(hk2 : 2 ≤ k) (hk_le_c : k ≤ c)
(hk_le : k ≤ ListNondegenerate.deg (G := G) v)
(hcard_lt : (ListNondegenerate.NeighborColors (G := G) (y := y) v).card < k)
(hu0 : u0 ∈ ListNondegenerate.Ne (G := G) v)
(hu1 : u1 ∈ ListNondegenerate.Ne (G := G) v)
(hu01 : u0 ≠ u1)
(hcol : y u0 = y u1) :
    ∃ y' : ListNondegenerate.Coloring (V := V) C,
      ListNondegenerate.IsListColoring (V := V) (C := C) L y' ∧
      ListNondegenerate.IsProper (G := G) y' ∧
      (Finset.univ.sum (fun v : V =>
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
            if ListNondegenerate.deg (G := G) v ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card
            else 0))) <
        (Finset.univ.sum (fun v : V =>
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
            if ListNondegenerate.deg (G := G) v ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
            else 0))) := by
  classical

  -- Obtain a vertex `u` among `{u0,u1}` and a new color `a` to recolor it.
  rcases
      ListNondegenerate.exists_color_for_recolor_from_duplicate_aux_badness
        (G := G) (D := D) (C := C) (c := c) (hc := hc) (hC := hC) (hΔ := hΔ)
        (L := L) (hL := hL) (y := y) (hyL := hyL) (hyP := hyP)
        (v := v) (u0 := u0) (u1 := u1) (k := k)
        hk2 hk_le_c hk_le hcard_lt hu0 hu1 hu01 hcol
    with
    ⟨u, hu, a, haLu, haNv, haNu, hmono⟩

  let y' : ListNondegenerate.Coloring (V := V) C :=
    ListNondegenerate.recolor (y := y) u a

  refine ⟨y', ?_, ?_, ?_⟩

  ·
    -- list coloring property
    simpa [y'] using
      ListNondegenerate.isListColoring_recolor (L := L) (y := y) (u := u) (a := a) hyL haLu

  ·
    -- properness after recolor
    have hAdj : ∀ w : V, G.Adj u w → a ≠ y w := by
      intro w hwAdj
      intro hEq
      apply haNu
      have hwNe : w ∈ ListNondegenerate.Ne (G := G) u := by
        simp [ListNondegenerate.Ne, hwAdj]
      have hyw : y w ∈ ListNondegenerate.NeighborColors (G := G) (y := y) u := by
        -- `w` is a neighbor of `u`, hence its color is in the neighbor-colors finset.
        simpa [ListNondegenerate.NeighborColors] using (Finset.mem_image_of_mem y hwNe)
      -- rewrite `y w` to `a` using `hEq`
      exact (by simpa [hEq.symm] using hyw)

    simpa [y'] using
      ListNondegenerate.isProper_recolor (G := G) (y := y) (u := u) (a := a) hyP hAdj

  ·
    -- strict decrease of the global badness sum
    let Ks : Finset ℕ := (Finset.range (c + 1)).filter (fun k => 2 ≤ k)
    let badAt (y0 : ListNondegenerate.Coloring (V := V) C) (t : V) : ℕ :=
      Ks.sum (fun k =>
        if ListNondegenerate.deg (G := G) t ≥ k then
          k - (ListNondegenerate.NeighborColors (G := G) (y := y0) t).card
        else 0)

    have hbadAt_le : ∀ t : V, badAt y' t ≤ badAt y t := by
      intro t
      -- this is exactly the monotonicity statement `hmono` from the auxiliary lemma
      simpa [badAt, Ks, y'] using (hmono t)

    have hcard_v :
        (ListNondegenerate.NeighborColors (G := G) (y := y') v).card =
          (ListNondegenerate.NeighborColors (G := G) (y := y) v).card + 1 := by
      -- depending on whether `u = u0` or `u = u1`, apply the card-increase lemma.
      cases hu with
      | inl hu0eq =>
          -- eliminate `u` (so that `y'` becomes `recolor y u0 a`)
          subst u
          simpa [y'] using
            (ListNondegenerate.card_neighborColors_recolor_of_duplicate (G := G) (y := y)
              (v := v) (u0 := u0) (u1 := u1) (a := a)
              hu0 hu1 hu01 hcol haNv)
      | inr hu1eq =>
          subst u
          simpa [y'] using
            (ListNondegenerate.card_neighborColors_recolor_of_duplicate (G := G) (y := y)
              (v := v) (u0 := u1) (u1 := u0) (a := a)
              hu1 hu0 hu01.symm hcol.symm haNv)

    have hbadAt_lt_v : badAt y' v < badAt y v := by
      -- show strict inequality for the inner sum at vertex `v`
      let m : ℕ := (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
      have hm_lt : m < k := by
        simpa [m] using hcard_lt
      have hm1_le : m + 1 ≤ k := Nat.succ_le_of_lt hm_lt
      have hk_mem : k ∈ Ks := by
        refine Finset.mem_filter.2 ?_
        refine ⟨?_, hk2⟩
        exact Finset.mem_range.2 (Nat.lt_succ_of_le hk_le_c)
      have hkdeg : ListNondegenerate.deg (G := G) v ≥ k := by
        simpa [ge_iff_le] using hk_le
      have hcard_v' :
          (ListNondegenerate.NeighborColors (G := G) (y := y') v).card = m + 1 := by
        simpa [m] using hcard_v

      have hterm_le :
          ∀ k' ∈ Ks,
            (if ListNondegenerate.deg (G := G) v ≥ k' then
                k' - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card
              else 0)
              ≤
              (if ListNondegenerate.deg (G := G) v ≥ k' then
                k' - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
              else 0) := by
        intro k' hk'
        by_cases hdeg : ListNondegenerate.deg (G := G) v ≥ k'
        ·
          have hcard_le :
              (ListNondegenerate.NeighborColors (G := G) (y := y) v).card ≤
                (ListNondegenerate.NeighborColors (G := G) (y := y') v).card := by
            have :
                (ListNondegenerate.NeighborColors (G := G) (y := y) v).card ≤
                  (ListNondegenerate.NeighborColors (G := G) (y := y) v).card + 1 :=
              Nat.le_succ _
            simpa [hcard_v] using this
          have hsub :
              k' - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card ≤
                k' - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card := by
            exact Nat.sub_le_sub_left hcard_le k'
          simpa [hdeg] using hsub
        ·
          simp [hdeg]

      have hterm_lt :
          (if ListNondegenerate.deg (G := G) v ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card
            else 0)
            <
            (if ListNondegenerate.deg (G := G) v ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
            else 0) := by
        -- deg v ≥ k, so reduce to strict inequality of subtractions
        have hsub_lt : k - (m + 1) < k - m := by
          have : m < m + 1 := Nat.lt_succ_self m
          exact (tsub_lt_tsub_iff_left_of_le hm1_le).2 this
        simpa [hkdeg, hcard_v', m] using hsub_lt

      have hsum_lt :
          Ks.sum (fun k' =>
              if ListNondegenerate.deg (G := G) v ≥ k' then
                k' - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card
              else 0)
            <
            Ks.sum (fun k' =>
              if ListNondegenerate.deg (G := G) v ≥ k' then
                k' - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
              else 0) := by
        refine Finset.sum_lt_sum ?_ ?_
        · intro k' hk'
          exact hterm_le k' hk'
        · exact ⟨k, hk_mem, hterm_lt⟩

      simpa [badAt] using hsum_lt

    have hglobal_lt :
        (Finset.univ.sum fun t : V => badAt y' t) <
          (Finset.univ.sum fun t : V => badAt y t) := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro t ht
        exact hbadAt_le t
      · exact ⟨v, by simp, hbadAt_lt_v⟩

    simpa [badAt, Ks] using hglobal_lt


theorem ListNondegenerate.badness_decrease_step {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {D C c : ℕ}
(hc : 2 ≤ c)
(hC : C = max (D + c * c - 1) ((D + 1) * c))
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D)
(L : ListNondegenerate.ListSystem (V := V) C)
(hL : ListNondegenerate.ListSystemHasCard (V := V) (C := C) L)
(y : ListNondegenerate.Coloring (V := V) C)
(hyL : ListNondegenerate.IsListColoring (V := V) (C := C) L y)
(hyP : ListNondegenerate.IsProper (G := G) y)
(hpos : (Finset.univ.sum (fun v : V =>
  ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
    if ListNondegenerate.deg (G := G) v ≥ k then
      k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
    else 0))) > 0) :
    ∃ y' : ListNondegenerate.Coloring (V := V) C,
      ListNondegenerate.IsListColoring (V := V) (C := C) L y' ∧
      ListNondegenerate.IsProper (G := G) y' ∧
      (Finset.univ.sum (fun v : V =>
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
            if ListNondegenerate.deg (G := G) v ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card
            else 0))) <
        (Finset.univ.sum (fun v : V =>
          ((Finset.range (c + 1)).filter (fun k => 2 ≤ k)).sum (fun k =>
            if ListNondegenerate.deg (G := G) v ≥ k then
              k - (ListNondegenerate.NeighborColors (G := G) (y := y) v).card
            else 0))) := by
  classical
  rcases ListNondegenerate.exists_v_k_of_badness_pos (G := G) (y := y) hpos with
    ⟨v, k, hk2, hk_le_c, hdeg_ge, hcard_lt⟩
  have hk_le_deg : k ≤ ListNondegenerate.deg (G := G) v := by
    exact hdeg_ge
  rcases
      ListNondegenerate.exists_two_neighbors_eq_color_of_card_neighborColors_lt (G := G)
        (y := y) (v := v) (k := k) hk_le_deg hcard_lt with
    ⟨u0, hu0Ne, u1, hu1Ne, hu01, hcol⟩
  rcases
      ListNondegenerate.recolor_from_duplicate (G := G) (D := D) (C := C) (c := c) hc hC hΔ L
        hL y hyL hyP (v := v) (u0 := u0) (u1 := u1) (k := k) hk2 hk_le_c hk_le_deg hcard_lt
        hu0Ne hu1Ne hu01 hcol with
    ⟨y', hy'L, hy'P, hlt⟩
  exact ⟨y', hy'L, hy'P, hlt⟩

theorem ListNondegenerate.exists_FNondegenerate_Lin_of_proper {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) {D C c : ℕ}
(hc : 2 ≤ c)
(hC : C = max (D + c * c - 1) ((D + 1) * c))
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D) :
    ∀ (L : ListNondegenerate.ListSystem (V := V) C),
      ListNondegenerate.ListSystemHasCard (V := V) (C := C) L →
      ∀ (y : ListNondegenerate.Coloring (V := V) C),
        ListNondegenerate.IsListColoring (V := V) (C := C) L y →
        ListNondegenerate.IsProper (G := G) y →
        ∃ (y' : ListNondegenerate.Coloring (V := V) C),
          ListNondegenerate.IsListColoring (V := V) (C := C) L y' ∧
          ListNondegenerate.IsProper (G := G) y' ∧
          ListNondegenerate.FNondegenerate (G := G) (V := V) (C := C) y' (ListNondegenerate.Lin c) := by
  classical
  -- Provide fintype instances for the palette and colorings.
  letI : Fintype (ListNondegenerate.Palette (V := V) C) := by
    classical
    unfold ListNondegenerate.Palette
    infer_instance
  letI : Fintype (ListNondegenerate.Coloring (V := V) C) := by
    classical
    unfold ListNondegenerate.Coloring
    infer_instance

  -- Define the finset of relevant k's (2 ≤ k ≤ c)
  let Ks : Finset ℕ := (Finset.range (c + 1)).filter (fun k => 2 ≤ k)

  -- Define the badness measure of a coloring
  let bad : ListNondegenerate.Coloring (V := V) C → ℕ := fun y' =>
    Finset.univ.sum (fun v : V =>
      Ks.sum (fun k =>
        if ListNondegenerate.deg (G := G) v ≥ k then
          k - (ListNondegenerate.NeighborColors (G := G) (y := y') v).card
        else 0))

  intro L hL
  intro y hyList hyProp

  -- Consider the finset of proper list-colorings
  let S : Finset (ListNondegenerate.Coloring (V := V) C) :=
    Finset.univ.filter (fun y' =>
      ListNondegenerate.IsListColoring (V := V) (C := C) L y' ∧
        ListNondegenerate.IsProper (G := G) y')

  have hyS : y ∈ S := by
    simp [S, hyList, hyProp]

  have hSnonempty : S.Nonempty := ⟨y, hyS⟩

  -- Choose a coloring minimizing `bad` among proper list-colorings
  obtain ⟨y0, hy0S, hy0min⟩ := Finset.exists_min_image S bad hSnonempty

  have hy0List : ListNondegenerate.IsListColoring (V := V) (C := C) L y0 := by
    have :
        ListNondegenerate.IsListColoring (V := V) (C := C) L y0 ∧
          ListNondegenerate.IsProper (G := G) y0 := by
      simpa [S] using (Finset.mem_filter.1 hy0S).2
    exact this.1

  have hy0Prop : ListNondegenerate.IsProper (G := G) y0 := by
    have :
        ListNondegenerate.IsListColoring (V := V) (C := C) L y0 ∧
          ListNondegenerate.IsProper (G := G) y0 := by
      simpa [S] using (Finset.mem_filter.1 hy0S).2
    exact this.2

  -- Show the minimal badness must be 0, otherwise we can improve it.
  have hbad0 : bad y0 = 0 := by
    by_contra hne
    have hpos : bad y0 > 0 := Nat.pos_of_ne_zero hne
    obtain ⟨y1, hy1List, hy1Prop, hy1lt⟩ :=
      ListNondegenerate.badness_decrease_step (G := G) (D := D) (C := C) (c := c)
        hc hC hΔ L hL y0 hy0List hy0Prop (by simpa [bad, Ks] using hpos)
    have hy1S : y1 ∈ S := by
      simp [S, hy1List, hy1Prop]
    have hle : bad y0 ≤ bad y1 := hy0min y1 hy1S
    exact (Nat.not_lt_of_ge hle) (by simpa [bad, Ks] using hy1lt)

  refine ⟨y0, hy0List, hy0Prop, ?_⟩

  -- Use the provided iff characterization of `FNondegenerate (Lin c)`.
  refine (ListNondegenerate.FNondegenerate_Lin_iff (G := G) (y := y0)).2 ?_
  intro k hk2 hkc v hvdeg

  -- Show k ∈ Ks
  have hk_mem : k ∈ Ks := by
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, hk2⟩
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hkc)

  -- From `bad y0 = 0`, every summand in the definition of `bad` is 0.
  have hsum0 :
      (Finset.univ.sum (fun v : V =>
        Ks.sum (fun k =>
          if ListNondegenerate.deg (G := G) v ≥ k then
            k - (ListNondegenerate.NeighborColors (G := G) (y := y0) v).card
          else 0))) = 0 := by
    simpa [bad] using hbad0

  have hv0 :
      Ks.sum (fun k =>
        if ListNondegenerate.deg (G := G) v ≥ k then
          k - (ListNondegenerate.NeighborColors (G := G) (y := y0) v).card
        else 0) = 0 := by
    have hall' := (Finset.sum_eq_zero_iff).1 hsum0
    have := hall' v (by simp)
    simpa using this

  have hterm0 :
      (if ListNondegenerate.deg (G := G) v ≥ k then
          k - (ListNondegenerate.NeighborColors (G := G) (y := y0) v).card
        else 0) = 0 := by
    have hallk := (Finset.sum_eq_zero_iff).1 hv0
    exact hallk k hk_mem

  have hsub0 :
      k - (ListNondegenerate.NeighborColors (G := G) (y := y0) v).card = 0 := by
    simpa [hvdeg] using hterm0

  exact (Nat.sub_eq_zero_iff_le).1 hsub0

theorem ListNondegenerate.exists_proper_list_coloring_Lin {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V)
{D C c : ℕ}
(hc : 2 ≤ c)
(hC : C = max (D + c * c - 1) ((D + 1) * c))
(hΔ : ∀ v : V, ListNondegenerate.deg (G := G) v ≤ D) :
    ∀ (L : ListNondegenerate.ListSystem (V := V) C),
      ListNondegenerate.ListSystemHasCard (V := V) (C := C) L →
      ∃ (y : ListNondegenerate.Coloring (V := V) C),
        ListNondegenerate.IsListColoring (V := V) (C := C) L y ∧
        ListNondegenerate.IsProper (G := G) y ∧
        ListNondegenerate.FNondegenerate (G := G) (V := V) (C := C) y (ListNondegenerate.Lin c) := by
  intro L hL
  classical
  have hC0 : D + 1 ≤ C := by
    have h1 : 1 ≤ c := by
      exact le_trans (by decide : (1 : ℕ) ≤ 2) hc
    have hmul : D + 1 ≤ (D + 1) * c := by
      -- (D+1)*1 ≤ (D+1)*c
      simpa [Nat.mul_one] using (Nat.mul_le_mul_left (D + 1) h1)
    have hmax : D + 1 ≤ max (D + c * c - 1) ((D + 1) * c) := by
      exact le_trans hmul (Nat.le_max_right _ _)
    -- rewrite `C` using `hC`
    simpa [hC] using hmax
  rcases ListNondegenerate.exists_proper_list_coloring_of_maxDegree
      (G := G) (D := D) (C := C) hΔ hC0 L hL with ⟨y, hyL, hyP⟩
  rcases ListNondegenerate.exists_FNondegenerate_Lin_of_proper
      (G := G) (D := D) (C := C) (c := c) hc hC hΔ
      L hL y hyL hyP with ⟨y', hy'L, hy'P, hy'F⟩
  exact ⟨y', hy'L, hy'P, hy'F⟩

