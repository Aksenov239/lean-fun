import LeanFun.Definitions

open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, m = Multiset.replicate (b ^ (b ^ j)) i }

lemma simple_lemma {A B : Prop} : A ∧ B → B :=
  fun h : A ∧ B => And.right h

theorem ball_A1_iff_card_le (R : ℕ) (m : FreeAbelianMonoid 1) : m ∈ Ball R (A 1) ↔ m.card ≤ R := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hlR, hlA, rfl⟩
    have hsum_card : ∀ l : List (FreeAbelianMonoid 1),
        (∀ x, x ∈ l → x ∈ A 1) → (l.sum).card = l.length := by
      intro l
      induction l with
      | nil =>
          intro hl
          simp
      | cons a t ih =>
          intro hl
          have ha_mem : a ∈ A 1 := hl a (by simp)
          rcases (by simpa [A] using ha_mem) with ⟨i, rfl⟩
          have ht : (t.sum).card = t.length := ih (by
            intro x hx
            exact hl x (by simp [hx]))
          simp [List.sum_cons, Multiset.card_add, ht]
    have : (l.sum).card = l.length := hsum_card l hlA
    exact le_trans (by simpa [this]) hlR
  · intro hmcard
    have hrepr : ∀ m : FreeAbelianMonoid 1,
        ∃ l : List (FreeAbelianMonoid 1),
          (∀ x, x ∈ l → x ∈ A 1) ∧ l.sum = m ∧ l.length = m.card := by
      intro m
      induction m using Multiset.induction_on with
      | empty =>
          refine ⟨[], ?_, ?_, ?_⟩
          · intro x hx
            cases hx
          · simp
          · simp
      | @cons a m ih =>
          rcases ih with ⟨l, hlA, hsum, hlen⟩
          refine ⟨({a} : Multiset (Fin 1)) :: l, ?_, ?_, ?_⟩
          · intro x hx
            rcases (List.mem_cons.1 hx) with rfl | hx'
            · exact ⟨a, rfl⟩
            · exact hlA x hx'
          · simpa [List.sum_cons, hsum, Multiset.singleton_add]
          · simpa [List.length_cons, hlen, Multiset.card_cons, Nat.succ_eq_add_one]
    rcases hrepr m with ⟨l, hlA, hsum, hlen⟩
    refine ⟨l, ?_, hlA, hsum⟩
    simpa [hlen] using hmcard

def doublyCoin (b : ℕ) (n : ℕ) : Prop := n = 1 ∨ ∃ j : ℕ, n = b ^ (b ^ j)

theorem doublyMacro_inter_ball_ncard (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) :
  ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 := by
  classical
  let N : ℕ := Nat.log b (Nat.log b x) + 1
  let f : Fin N → FreeAbelianMonoid 1 :=
    fun j => Multiset.replicate (b ^ (b ^ (j : ℕ))) (0 : Fin 1)
  have hb1 : 1 < b := by
    omega
  have hb0 : 0 < b := by
    omega
  have hxpos : 0 < x := by
    have hpowpos : 0 < b ^ b := by
      exact pow_pos hb0 b
    exact lt_of_lt_of_le hpowpos hx
  have hx0 : x ≠ 0 := Nat.ne_of_gt hxpos
  have hb1le : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hbne0 : b ≠ 0 := by
    omega
  have hble_pow : b ≤ b ^ b := le_self_pow hb1le hbne0
  have hble_x : b ≤ x := le_trans hble_pow hx
  have hlogpos : 0 < Nat.log b x := Nat.log_pos hb1 hble_x
  have hlogne0 : Nat.log b x ≠ 0 := Nat.ne_of_gt hlogpos

  have hEq : Set.range f = (DoublyMacroSet b) ∩ Ball x (A 1) := by
    ext m
    constructor
    · intro hm
      rcases hm with ⟨j, rfl⟩
      refine And.intro ?_ ?_
      · -- membership in DoublyMacroSet
        refine ⟨(0 : Fin 1), (j : ℕ), rfl⟩
      · -- membership in Ball
        have hjle : (j : ℕ) ≤ Nat.log b (Nat.log b x) := by
          have : (j : ℕ) < Nat.log b (Nat.log b x) + 1 := j.is_lt
          exact Nat.lt_succ_iff.mp this
        have hpow1 : b ^ (j : ℕ) ≤ Nat.log b x := by
          exact Nat.pow_le_of_le_log (b := b) (x := (j : ℕ)) (y := Nat.log b x) hlogne0 hjle
        have hpow2 : b ^ (b ^ (j : ℕ)) ≤ x := by
          exact Nat.pow_le_of_le_log (b := b) (x := b ^ (j : ℕ)) (y := x) hx0 hpow1
        have hcardle : (Multiset.replicate (b ^ (b ^ (j : ℕ))) (0 : Fin 1)).card ≤ x := by
          simpa using hpow2
        exact (ball_A1_iff_card_le x (Multiset.replicate (b ^ (b ^ (j : ℕ))) (0 : Fin 1))).2 hcardle
    · intro hm
      rcases hm with ⟨hmD, hmB⟩
      rcases hmD with ⟨i, j0, rfl⟩
      have hi0 : i = (0 : Fin 1) := Subsingleton.elim i 0
      subst hi0
      have hcardle : (Multiset.replicate (b ^ (b ^ j0)) (0 : Fin 1)).card ≤ x :=
        (ball_A1_iff_card_le x (Multiset.replicate (b ^ (b ^ j0)) (0 : Fin 1))).1 hmB
      have hpow : b ^ (b ^ j0) ≤ x := by
        simpa using hcardle
      have hpow' : b ^ j0 ≤ Nat.log b x := by
        exact (Nat.pow_le_iff_le_log (b := b) hb1 (x := b ^ j0) (y := x) hx0).1 hpow
      have hj0_le : j0 ≤ Nat.log b (Nat.log b x) := by
        exact (Nat.pow_le_iff_le_log (b := b) hb1 (x := j0) (y := Nat.log b x) hlogne0).1 hpow'
      let jfin : Fin N := ⟨j0, by
        dsimp [N]
        exact Nat.lt_succ_of_le hj0_le⟩
      refine ⟨jfin, ?_⟩
      simpa [f, jfin]

  have hf : Function.Injective f := by
    intro j1 j2 hj
    apply Fin.ext
    have hpow : b ^ (b ^ (j1 : ℕ)) = b ^ (b ^ (j2 : ℕ)) :=
      (Multiset.replicate_left_injective (0 : Fin 1)) hj
    have hpow' : b ^ (j1 : ℕ) = b ^ (j2 : ℕ) := (Nat.pow_right_injective hb) hpow
    have hval : (j1 : ℕ) = (j2 : ℕ) := (Nat.pow_right_injective hb) hpow'
    exact hval

  calc
    ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard = (Set.range f).ncard := by
      simpa [hEq]
    _ = Nat.card (Fin N) := by
      simpa using (Set.ncard_range_of_injective (f := f) hf)
    _ = N := by
      simp [Nat.card_fin]
    _ = Nat.log b (Nat.log b x) + 1 := by
      rfl

def doublyRep (b s N : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ s ∧ (∀ n ∈ l, doublyCoin b n) ∧ l.sum = N

theorem doublyRep_add_mul (b m s N q : ℕ) (hm : doublyCoin b m) (hrep : doublyRep b s N) :
  doublyRep b (s + q) (q * m + N) := by
  classical
  rcases hrep with ⟨l, hl_len, hl_coin, hl_sum⟩
  let l' : List ℕ := List.replicate q m ++ l
  refine ⟨l', ?_, ?_, ?_⟩
  ·
    have h := Nat.add_le_add_left hl_len q
    simpa [l', List.length_append, List.length_replicate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  ·
    intro n hn
    have hn' : n ∈ List.replicate q m ++ l := by
      simpa [l'] using hn
    rcases List.mem_append.mp hn' with hnrep | hnl
    ·
      have hn_eq : n = m := by
        exact List.eq_of_mem_replicate hnrep
      simpa [hn_eq] using hm
    ·
      exact hl_coin n hnl
  ·
    -- sum
    simp [l', List.sum_append, List.sum_replicate, hl_sum, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem doublyRep_mono_s (b s t N : ℕ) : doublyRep b s N → s ≤ t → doublyRep b t N := by
  intro h hs
  -- unfold definition
  rcases h with ⟨l, hl_len, hl_coin, hl_sum⟩
  refine ⟨l, ?_, hl_coin, hl_sum⟩
  exact le_trans hl_len hs

def doubly_m (b k : ℕ) : ℕ := b ^ (b ^ k)

theorem doublyCoin_mk (b k : ℕ) : doublyCoin b (doubly_m b k) := by
  unfold doublyCoin
  right
  refine ⟨k, ?_⟩
  unfold doubly_m
  rfl


def doubly_T (b : ℕ) : ℕ → ℕ
  | 0 => b - 1
  | k + 1 => (doubly_m b k) ^ (b - 1) - 1 + doubly_T b k

theorem doubly_T_succ (b k : ℕ) : doubly_T b (k + 1) = (doubly_m b k) ^ (b - 1) - 1 + doubly_T b k :=   rfl

theorem doubly_T_zero (b : ℕ) : doubly_T b 0 = b - 1 :=   rfl


theorem doublyRep_mk_sub_one (b : ℕ) (hb : 2 ≤ b) :
  ∀ k : ℕ, doublyRep b (doubly_T b k) (doubly_m b k - 1) := by
  intro k

  -- If an element lies in a replicated list, it must equal the replicated value.
  have mem_replicate_eq {a x : ℕ} {n : ℕ} (hx : x ∈ List.replicate n a) : x = a := by
    have hx' : x ∈ ([a] : List ℕ) := (List.replicate_subset_singleton n a) hx
    -- `[a]` is `pure a`.
    have hx'' : x ∈ (pure a : List ℕ) := by
      simpa using hx'
    exact (List.mem_pure x a).1 hx''

  induction k with
  | zero =>
      refine ⟨List.replicate (b - 1) 1, ?_, ?_, ?_⟩
      · -- length bound
        simp [doubly_T_zero]
      · -- coin condition (all entries are 1)
        intro n hn
        have hn1 : n = 1 := mem_replicate_eq hn
        exact Or.inl hn1
      · -- sum
        simp [List.sum_const_nat, doubly_m]

  | succ k ih =>
      rcases ih with ⟨l0, hl0_len, hl0_coin, hl0_sum⟩
      set mk : ℕ := doubly_m b k with hmk

      have hl0_sum' : l0.sum = mk - 1 := by
        simpa [hmk.symm] using hl0_sum

      have hT : doubly_T b (k + 1) = mk ^ (b - 1) - 1 + doubly_T b k := by
        simpa [hmk.symm] using (doubly_T_succ b k)

      refine ⟨List.replicate (mk ^ (b - 1) - 1) mk ++ l0, ?_, ?_, ?_⟩

      · -- length bound
        have hlen : (mk ^ (b - 1) - 1) + l0.length ≤ (mk ^ (b - 1) - 1) + doubly_T b k :=
          Nat.add_le_add_left hl0_len (mk ^ (b - 1) - 1)
        simpa [List.length_append, List.length_replicate, hT, Nat.add_assoc] using hlen

      · -- coin condition
        intro n hn
        have hn' : n ∈ List.replicate (mk ^ (b - 1) - 1) mk ∨ n ∈ l0 :=
          (List.mem_append.1 hn)
        cases hn' with
        | inl hnrep =>
            have hnm : n = mk := mem_replicate_eq hnrep
            subst hnm
            refine Or.inr ?_
            refine ⟨k, ?_⟩
            -- unfold mk
            simp [hmk, doubly_m]
        | inr hnl0 =>
            exact hl0_coin n hnl0

      · -- sum
        have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
        have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb1

        have hmk1 : 1 ≤ mk := by
          simpa [hmk, doubly_m] using (one_le_pow₀ hb1 : 1 ≤ b ^ (b ^ k))

        have hab : mk ≤ mk ^ (b - 1) * mk := by
          have hpow : 1 ≤ mk ^ (b - 1) := one_le_pow₀ hmk1
          exact le_mul_of_one_le_left (show 0 ≤ mk from Nat.zero_le _) hpow

        have hgeo : (mk ^ (b - 1) - 1) * mk + (mk - 1) = mk ^ b - 1 := by
          calc
            (mk ^ (b - 1) - 1) * mk + (mk - 1)
                = (mk ^ (b - 1) * mk - mk) + (mk - 1) := by
                    simpa using
                      congrArg (fun t => t + (mk - 1)) (tsub_one_mul (mk ^ (b - 1)) mk)
            _ = mk ^ (b - 1) * mk - 1 := by
                    simpa using
                      (tsub_add_tsub_cancel hab hmk1 :
                        mk ^ (b - 1) * mk - mk + (mk - 1) = mk ^ (b - 1) * mk - 1)
            _ = mk ^ (b - 1 + 1) - 1 := by
                    simpa using
                      congrArg (fun t => t - 1) ((pow_succ mk (b - 1)).symm)
            _ = mk ^ b - 1 := by
                    simpa [hbsub]

        have hm_succ : doubly_m b (k + 1) = mk ^ b := by
          -- expand `doubly_m` and use `mk = doubly_m b k`
          simp [doubly_m, hmk, pow_succ, pow_mul]

        calc
          (List.replicate (mk ^ (b - 1) - 1) mk ++ l0).sum
              = (List.replicate (mk ^ (b - 1) - 1) mk).sum + l0.sum := by
                  simp [List.sum_append]
          _ = (mk ^ (b - 1) - 1) * mk + l0.sum := by
                  simp [List.sum_const_nat]
          _ = (mk ^ (b - 1) - 1) * mk + (mk - 1) := by
                  simp [hl0_sum']
          _ = mk ^ b - 1 := by
                  simpa using hgeo
          _ = doubly_m b (k + 1) - 1 := by
                  simpa [hm_succ]

theorem doubly_m_ge_two (b k : ℕ) (hb : 2 ≤ b) : 2 ≤ doubly_m b k := by
  unfold doubly_m
  have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hk : 1 ≤ b ^ k := by
    exact one_le_pow₀ hb1
  have hpow : b ^ 1 ≤ b ^ (b ^ k) := by
    exact pow_le_pow_right' hb1 hk
  have hbpow : 2 ≤ b ^ 1 := by
    simpa [Nat.pow_one] using hb
  exact le_trans hbpow hpow

theorem doubly_m_mono (b : ℕ) (hb : 2 ≤ b) : Monotone (doubly_m b) := by
  intro j k hjk
  have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hpow : b ^ j ≤ b ^ k := pow_le_pow_right' hb1 hjk
  simpa [doubly_m] using (pow_le_pow_right' hb1 hpow)

theorem doubly_m_pos (b k : ℕ) (hb : 2 ≤ b) : 0 < doubly_m b k := by
  unfold doubly_m
  have hb0 : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  simpa using pow_pos hb0 (b ^ k)


theorem doubly_T_ge_self_fixed (b : ℕ) (hb : 2 ≤ b) : ∀ k : ℕ, k ≤ doubly_T b k := by
  intro k
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      -- unfold the recursion for doubly_T
      rw [doubly_T_succ b k]
      -- show `1 ≤ b`
      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
      have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
      have hbne0 : b ≠ 0 := ne_of_gt hbpos
      have hbpow_ne0 : b ^ k ≠ 0 := pow_ne_zero k hbne0
      have hb_le_m : b ≤ doubly_m b k := by
        dsimp [doubly_m]
        exact le_self_pow hb1 hbpow_ne0
      have hm2 : 2 ≤ doubly_m b k := le_trans hb hb_le_m
      have hm1 : 1 ≤ doubly_m b k := le_trans (by decide : (1 : ℕ) ≤ 2) hm2
      have hbsub_ne0 : b - 1 ≠ 0 := by
        have hbsub_ge1 : 1 ≤ b - 1 := by
          have h := tsub_le_tsub_right hb 1
          simpa using h
        have hbsub_pos : 0 < b - 1 := lt_of_lt_of_le (Nat.succ_pos 0) hbsub_ge1
        exact ne_of_gt hbsub_pos
      have hm_le_pow : doubly_m b k ≤ (doubly_m b k) ^ (b - 1) :=
        le_self_pow hm1 hbsub_ne0
      have hpow2 : 2 ≤ (doubly_m b k) ^ (b - 1) := le_trans hm2 hm_le_pow
      have hpow1 : 1 ≤ (doubly_m b k) ^ (b - 1) - 1 := by
        have h := tsub_le_tsub_right hpow2 1
        simpa using h
      have hk' : 1 + k ≤ (doubly_m b k) ^ (b - 1) - 1 + doubly_T b k :=
        add_le_add hpow1 ih
      -- rewrite `1 + k` as `k + 1` / `Nat.succ k`
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hk'

theorem doubly_m_succ (b k : ℕ) : doubly_m b (k + 1) = (doubly_m b k) ^ b := by
  unfold doubly_m
  rw [pow_succ, pow_mul]

theorem doublyRep_coin_le_mk (b : ℕ) (hb : 2 ≤ b) :
  ∀ {k n : ℕ}, doublyCoin b n → n ≤ doubly_m b (k + 1) - 1 → n ≤ doubly_m b k := by
  intro k n hcoin hn
  rcases hcoin with rfl | ⟨j, rfl⟩
  · have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hb
    have hpos : 0 < doubly_m b k := by
      dsimp [doubly_m]
      exact Nat.pow_pos (n := b ^ k) hbpos
    exact (Nat.succ_le_iff).2 hpos
  · have hmono : Monotone (doubly_m b) := doubly_m_mono b hb
    have hjle : j ≤ k := by
      apply Nat.le_of_not_gt
      intro hklt
      have hk1le : k + 1 ≤ j := Nat.succ_le_of_lt hklt
      have hle : doubly_m b (k + 1) ≤ doubly_m b j := hmono hk1le
      have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hb
      have hmpos : 0 < doubly_m b (k + 1) := by
        dsimp [doubly_m]
        exact Nat.pow_pos (n := b ^ (k + 1)) hbpos
      have hsub : doubly_m b (k + 1) - 1 < doubly_m b (k + 1) :=
        Nat.sub_lt_self (Nat.succ_pos 0) hmpos
      have hnlt : b ^ (b ^ j) < doubly_m b (k + 1) := lt_of_le_of_lt hn hsub
      have hle' : doubly_m b (k + 1) ≤ b ^ (b ^ j) := by
        simpa [doubly_m] using hle
      exact lt_irrefl _ (lt_of_le_of_lt hle' hnlt)
    have hle : doubly_m b j ≤ doubly_m b k := hmono hjle
    simpa [doubly_m] using hle

theorem doubly_m_zero (b : ℕ) : doubly_m b 0 = b := by
  simp [doubly_m]

theorem doublyRep_of_lt_mk (b : ℕ) (hb : 2 ≤ b) :
  ∀ k N : ℕ, N < doubly_m b k → doublyRep b (doubly_T b k) N := by
  intro k
  induction k with
  | zero =>
      intro N hN
      have hNb : N < b := by
        exact lt_of_lt_of_eq hN (doubly_m_zero b)
      refine ⟨List.replicate N 1, ?_, ?_, ?_⟩
      · have hle : N ≤ b - 1 := Nat.le_pred_of_lt hNb
        simpa [List.length_replicate, doubly_T_zero] using hle
      · intro n hn
        have hn1 : n = 1 := by
          simpa using (List.eq_of_mem_replicate hn)
        exact Or.inl hn1
      · simp [List.sum_replicate]
  | succ k ih =>
      intro N hN
      set mk : ℕ := doubly_m b k with hmk
      have hb0 : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
      have hmk_pos : 0 < mk := by
        rw [hmk, doubly_m]
        exact pow_pos hb0 (b ^ k)
      have h_m_eq : doubly_m b (k + 1) = mk ^ b := by
        calc
          doubly_m b (k + 1) = (doubly_m b k) ^ b := by
            simpa using (doubly_m_succ b k)
          _ = mk ^ b := by
            rw [hmk.symm]
      have hN_mkpow : N < mk ^ b := lt_of_lt_of_eq hN h_m_eq
      set q : ℕ := N / mk with hq
      set r : ℕ := N % mk with hr
      have hr_lt : r < mk := by
        simpa [hr] using Nat.mod_lt N hmk_pos
      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
      have hb_eq : b = (b - 1) + 1 := (Nat.sub_add_cancel hb1).symm
      have hN_pow' : N < mk ^ ((b - 1) + 1) := by
        exact lt_of_lt_of_eq hN_mkpow (congrArg (fun e => mk ^ e) hb_eq)
      have hN_mul : N < mk ^ (b - 1) * mk := by
        exact lt_of_lt_of_eq hN_pow' (pow_succ mk (b - 1))
      have hN_mul' : N < mk * mk ^ (b - 1) := by
        exact lt_of_lt_of_eq hN_mul (Nat.mul_comm (mk ^ (b - 1)) mk)
      have hq_lt : q < mk ^ (b - 1) := by
        have : N / mk < mk ^ (b - 1) := Nat.div_lt_of_lt_mul hN_mul'
        simpa [hq] using this
      rcases ih r hr_lt with ⟨lr, hlrlen, hlrcoin, hlrsum⟩
      refine ⟨List.replicate q mk ++ lr, ?_, ?_, ?_⟩
      · have hq_le : q ≤ mk ^ (b - 1) - 1 := Nat.le_pred_of_lt hq_lt
        have hlen' : q + lr.length ≤ mk ^ (b - 1) - 1 + doubly_T b k :=
          Nat.add_le_add hq_le hlrlen
        have hT : doubly_T b (k + 1) = mk ^ (b - 1) - 1 + doubly_T b k := by
          calc
            doubly_T b (k + 1) = (doubly_m b k) ^ (b - 1) - 1 + doubly_T b k := by
              simpa using (doubly_T_succ b k)
            _ = mk ^ (b - 1) - 1 + doubly_T b k := by
              rw [hmk.symm]
        have hlen_q : q + lr.length ≤ doubly_T b (k + 1) :=
          le_trans hlen' (le_of_eq hT.symm)
        simpa [List.length_append, List.length_replicate] using hlen_q
      · intro n hn
        have hn' : n ∈ List.replicate q mk ∨ n ∈ lr := by
          exact (List.mem_append.1 hn)
        cases hn' with
        | inl hnrep =>
            have hnmk : n = mk := by
              simpa using (List.eq_of_mem_replicate hnrep)
            subst hnmk
            refine Or.inr ?_
            refine ⟨k, ?_⟩
            rw [hmk, doubly_m]
        | inr hnlr =>
            exact hlrcoin n hnlr
      · calc
          (List.replicate q mk ++ lr).sum = (List.replicate q mk).sum + lr.sum := by
            simp [List.sum_append]
          _ = mk * q + r := by
            simp [hlrsum, List.sum_replicate, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc]
          _ = N := by
            simpa [hq, hr] using (Nat.div_add_mod N mk)

theorem doublyRep_cover_affine (b : ℕ) (hb : 2 ≤ b) :
  ∀ (k s N : ℕ), doubly_T b k ≤ s →
    N < (s - doubly_T b k + 1) * doubly_m b k →
    doublyRep b s N := by
  intro k s N hTs hN
  set T : ℕ := doubly_T b k with hT
  set m : ℕ := doubly_m b k with hm
  set q : ℕ := N / m with hq
  set r : ℕ := N % m with hr
  have hT_le_s : T ≤ s := by
    simpa [hT] using hTs
  have hmpos : 0 < m := by
    simpa [hm] using doubly_m_pos b k hb
  have hrlt : r < m := by
    simpa [hr] using Nat.mod_lt N hmpos
  have hrep_r : doublyRep b T r := by
    have hrlt' : r < doubly_m b k := by
      simpa [hm] using hrlt
    have hrep := doublyRep_of_lt_mk b hb k r hrlt'
    simpa [hT] using hrep
  have hmcoin : doublyCoin b m := by
    simpa [hm] using doublyCoin_mk b k
  have hrep_Tq : doublyRep b (T + q) (q * m + r) := by
    exact doublyRep_add_mul b m T r q hmcoin hrep_r
  have hdivmod : q * m + r = N := by
    have h := Nat.div_add_mod N m
    have h' : (N / m) * m + N % m = N := by
      simpa [Nat.mul_comm] using h
    simpa [hq, hr] using h'
  have hqmul_le : q * m ≤ N := by
    have hle : q * m ≤ q * m + r := by
      exact self_le_add_right (q * m) r
    simpa [hdivmod] using hle
  have hN' : N < (s - T + 1) * m := by
    simpa [hT, hm] using hN
  have hq_lt : q < s - T + 1 := by
    by_contra hq_ge
    have hAq : s - T + 1 ≤ q := le_of_not_gt hq_ge
    have hmul : (s - T + 1) * m ≤ q * m := Nat.mul_le_mul_right m hAq
    have hA_le_N : (s - T + 1) * m ≤ N := le_trans hmul hqmul_le
    exact (Nat.not_le_of_gt hN') hA_le_N
  have hqle : q ≤ s - T := by
    apply Order.le_of_lt_succ
    simpa [Nat.succ_eq_add_one] using hq_lt
  have hTqle : T + q ≤ s := by
    have hle : T + q ≤ T + (s - T) := Nat.add_le_add_left hqle T
    simpa [Nat.add_sub_of_le hT_le_s] using hle
  have hrep_N : doublyRep b (T + q) N := by
    simpa [hdivmod] using hrep_Tq
  exact doublyRep_mono_s b (T + q) s N hrep_N hTqle

theorem doubly_T_le_m_sub_one (b : ℕ) (hb : 2 ≤ b) : ∀ k : ℕ, doubly_T b k ≤ doubly_m b k - 1 := by
  intro k
  induction k with
  | zero =>
      simpa [doubly_T_zero, doubly_m_zero]
  | succ k ih =>
      rw [doubly_T_succ b k, doubly_m_succ b k]
      set a : ℕ := doubly_m b k with ha
      have ih' : doubly_T b k ≤ a - 1 := by
        simpa [ha] using ih
      have hstep1 : a ^ (b - 1) - 1 + doubly_T b k ≤ a ^ (b - 1) - 1 + (a - 1) := by
        exact Nat.add_le_add_left ih' (a ^ (b - 1) - 1)

      have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
      have hb1 : 1 ≤ b := Nat.succ_le_of_lt hbpos
      have hapos : 0 < a := by
        rw [ha]
        simp only [doubly_m]
        exact Nat.pow_pos (n := b ^ k) hbpos
      have ha1 : 1 ≤ a := Nat.succ_le_of_lt hapos
      have hpowpos : 0 < a ^ (b - 1) := Nat.pow_pos (n := b - 1) hapos
      have hpow1 : 1 ≤ a ^ (b - 1) := Nat.succ_le_of_lt hpowpos

      have hmul : a - 1 ≤ a ^ (b - 1) * (a - 1) := by
        have h := Nat.mul_le_mul_right (a - 1) hpow1
        simpa [Nat.one_mul] using h

      have hstep2 : a ^ (b - 1) - 1 + (a - 1) ≤ a ^ b - 1 := by
        have hadd : a ^ (b - 1) - 1 + (a - 1) ≤ a ^ (b - 1) - 1 + a ^ (b - 1) * (a - 1) :=
          Nat.add_le_add_left hmul (a ^ (b - 1) - 1)

        have hEq : a ^ (b - 1) - 1 + a ^ (b - 1) * (a - 1) = a ^ b - 1 := by
          have hx : 1 ≤ a ^ (b - 1) := hpow1

          have hsub :
              a ^ (b - 1) - 1 + a ^ (b - 1) * (a - 1)
                = a ^ (b - 1) + a ^ (b - 1) * (a - 1) - 1 := by
            calc
              a ^ (b - 1) - 1 + a ^ (b - 1) * (a - 1)
                  = a ^ (b - 1) * (a - 1) + (a ^ (b - 1) - 1) := by
                      simpa using
                        Nat.add_comm (a ^ (b - 1) - 1) (a ^ (b - 1) * (a - 1))
              _ = a ^ (b - 1) * (a - 1) + a ^ (b - 1) - 1 := by
                      simpa using (Nat.add_sub_assoc hx (a ^ (b - 1) * (a - 1))).symm
              _ = a ^ (b - 1) + a ^ (b - 1) * (a - 1) - 1 := by
                      rw [Nat.add_comm (a ^ (b - 1) * (a - 1)) (a ^ (b - 1))]

          have hfactor : a ^ (b - 1) + a ^ (b - 1) * (a - 1) = a ^ (b - 1) * (1 + (a - 1)) := by
            simpa [Nat.mul_add, Nat.mul_one] using
              (Nat.mul_add (a ^ (b - 1)) 1 (a - 1)).symm

          have hone : 1 + (a - 1) = a := by
            calc
              1 + (a - 1) = (a - 1) + 1 := by
                simpa using Nat.add_comm 1 (a - 1)
              _ = a := Nat.sub_add_cancel ha1

          have hpow : a ^ (b - 1) * a = a ^ b := by
            calc
              a ^ (b - 1) * a = a ^ (b - 1 + 1) := by
                simpa using (pow_succ a (b - 1)).symm
              _ = a ^ b := by
                simpa [Nat.sub_add_cancel hb1]

          calc
            a ^ (b - 1) - 1 + a ^ (b - 1) * (a - 1)
                = a ^ (b - 1) + a ^ (b - 1) * (a - 1) - 1 := hsub
            _ = a ^ (b - 1) * (1 + (a - 1)) - 1 := by
                exact congrArg (fun t => t - 1) hfactor
            _ = a ^ (b - 1) * a - 1 := by
                rw [hone]
            _ = a ^ b - 1 := by
                exact congrArg (fun t => t - 1) hpow

        exact le_trans hadd (le_of_eq hEq)

      exact le_trans hstep1 hstep2

theorem doublyRep_mk_sub_one_lower_bound (b : ℕ) (hb : 2 ≤ b) :
  ∀ (k s : ℕ), doublyRep b s (doubly_m b k - 1) → doubly_T b k ≤ s := by
  intro k s hrep
  classical
  induction k generalizing s with
  | zero =>
      rcases hrep with ⟨l, hls, hcoin, hsum⟩
      have hsum' : l.sum = b - 1 := by
        simpa [doubly_m_zero b] using hsum
      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
      have hall1 : ∀ n ∈ l, n = 1 := by
        intro n hn
        rcases hcoin n hn with h1 | ⟨j, hj⟩
        · exact h1
        ·
          have hnle : n ≤ l.sum := List.le_sum_of_mem hn
          have hExp : (1 : ℕ) ≤ b ^ j := by
            simpa using (one_le_pow₀ hb1 (n := j))
          have hpow : b ^ 1 ≤ b ^ (b ^ j) := pow_le_pow_right' hb1 hExp
          have hb_le_n : b ≤ n := by
            simpa [hj, pow_one] using hpow
          have hb_le_sum : b ≤ l.sum := le_trans hb_le_n hnle
          have hb_le_bsub1 : b ≤ b - 1 := by
            simpa [hsum'] using hb_le_sum
          have hlt : b - 1 < b := by omega
          have : False := (not_le_of_lt hlt) hb_le_bsub1
          exact False.elim this
      have hsum_len : l.sum = l.length := by
        have h :=
          List.sum_eq_card_nsmul (l := l) (m := (1 : ℕ)) (by
            intro n hn
            exact hall1 n hn)
        simpa [nsmul_eq_mul] using h
      have hbsub1_le_s : b - 1 ≤ s := by
        have hlen_eq : l.length = b - 1 := by
          simpa [hsum'] using hsum_len.symm
        simpa [hlen_eq] using hls
      simpa [doubly_T_zero] using hbsub1_le_s
  | succ k ih =>
      rcases hrep with ⟨l, hls, hcoin, hsum⟩
      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb

      set x : ℕ := doubly_m b k with hx
      set q : ℕ := x ^ (b - 1) - 1 with hq

      let lx : List ℕ := l.filter (fun n => n = x)
      let lr : List ℕ := l.filter (fun n => n ≠ x)

      have hlx_mem : ∀ n ∈ lx, n = x := by
        intro n hn
        have hn' : n ∈ l ∧ n = x := by
          simpa [lx] using hn
        exact hn'.2

      have hlx_sum : lx.sum = lx.length * x := by
        have h := List.sum_eq_card_nsmul (l := lx) (m := x) (by
          intro n hn
          exact hlx_mem n hn)
        simpa [nsmul_eq_mul] using h

      have hl_len : l.length = lx.length + lr.length := by
        simpa [lx, lr] using (List.length_eq_length_filter_add (l := l) (f := fun n : ℕ => n = x))

      have hl_sum : lx.sum + lr.sum = l.sum := by
        simpa [lx, lr] using
          (List.sum_map_filter_add_sum_map_filter_not (l := l) (f := fun n : ℕ => n) (p := fun n : ℕ => n = x))

      have hsum' : l.sum = x ^ b - 1 := by
        simpa [hx, doubly_m_succ b k] using hsum

      have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
      have hxpos : 0 < x := by
        simpa [hx, doubly_m] using pow_pos hbpos (b ^ k)
      have hx1 : 1 ≤ x := Nat.succ_le_iff.2 hxpos
      have hpow1 : 1 ≤ x ^ (b - 1) := one_le_pow₀ hx1

      have hb_eq : b - 1 + 1 = b := Nat.sub_add_cancel hb1
      have hxpow : x ^ b = x ^ (b - 1) * x := by
        have := pow_succ x (b - 1)
        simpa [hb_eq] using this

      have hdecomp : q * x + (x - 1) = x ^ b - 1 := by
        set A : ℕ := x ^ (b - 1) with hA
        have hxle : x ≤ A * x := by
          have := Nat.mul_le_mul_right x hpow1
          simpa [A, Nat.one_mul] using this
        calc
          q * x + (x - 1) = (A - 1) * x + (x - 1) := by
            simp [hq, hA]
          _ = (A * x - x) + (x - 1) := by
            simpa [tsub_one_mul]
          _ = (A * x - x + x) - 1 := by
            simpa [Nat.add_assoc] using (Nat.add_sub_assoc hx1 (A * x - x)).symm
          _ = A * x - 1 := by
            simp [Nat.sub_add_cancel hxle, Nat.add_assoc]
          _ = x ^ b - 1 := by
            simpa [hA, hxpow]

      have hsum_decomp : l.sum = q * x + (x - 1) := by
        calc
          l.sum = x ^ b - 1 := hsum'
          _ = q * x + (x - 1) := by
            symm
            exact hdecomp

      have hlx_le_q : lx.length ≤ q := by
        have hxpowb_pos : 0 < x ^ b := pow_pos hxpos b
        have hlsum_lt : l.sum < x ^ b := by
          have : x ^ b - 1 < x ^ b := tsub_lt_self hxpowb_pos (by decide : (0 : ℕ) < 1)
          simpa [hsum'] using this
        by_contra hcontra
        have hlt : q < lx.length := lt_of_not_ge hcontra
        have hge : q + 1 ≤ lx.length := Nat.succ_le_iff.2 hlt
        have hmul : (q + 1) * x ≤ lx.sum := by
          have := Nat.mul_le_mul_right x hge
          simpa [hlx_sum, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
        have hlx_sum_le : lx.sum ≤ l.sum := by
          have : lx.sum ≤ lx.sum + lr.sum := Nat.le_add_right _ _
          simpa [hl_sum] using this
        have hxpow_le : x ^ b ≤ l.sum := by
          have hq1 : q + 1 = x ^ (b - 1) := by
            have : (x ^ (b - 1) - 1) + 1 = x ^ (b - 1) := Nat.sub_add_cancel hpow1
            simpa [hq] using this
          have hqmul : (q + 1) * x = x ^ b := by
            calc
              (q + 1) * x = (x ^ (b - 1)) * x := by
                simpa [hq1]
              _ = x ^ b := by
                simpa [hxpow] using hxpow.symm
          have : (q + 1) * x ≤ l.sum := le_trans hmul hlx_sum_le
          simpa [hqmul] using this
        exact (not_lt_of_ge hxpow_le) hlsum_lt

      by_cases hxq' : lx.length = q
      ·
        have hlr_sum : lr.sum = x - 1 := by
          have htemp : q * x + lr.sum = l.sum := by
            simpa [hlx_sum, hxq'] using hl_sum
          have hmain : q * x + lr.sum = q * x + (x - 1) := by
            simpa [hsum_decomp] using htemp
          exact Nat.add_left_cancel hmain

        have hrep_lr : doublyRep b lr.length (x - 1) := by
          refine ⟨lr, ?_⟩
          refine ⟨le_rfl, ?_, hlr_sum⟩
          intro n hn
          have hn' : n ∈ l := List.mem_of_mem_filter hn
          exact hcoin n hn'

        have hTk_le : doubly_T b k ≤ lr.length := by
          have hrep' : doublyRep b lr.length (doubly_m b k - 1) := by
            simpa [hx] using hrep_lr
          exact ih _ hrep'

        have hq_lr : q + lr.length = l.length := by
          simpa [hxq'] using hl_len.symm

        have hlen_ge : q + doubly_T b k ≤ l.length := by
          have : q + doubly_T b k ≤ q + lr.length := Nat.add_le_add_left hTk_le q
          simpa [hq_lr] using this

        have hTsucc : doubly_T b (k + 1) = q + doubly_T b k := by
          simpa [hq, hx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (doubly_T_succ b k)

        have : doubly_T b (k + 1) ≤ l.length := by
          simpa [hTsucc] using hlen_ge
        exact le_trans this hls
      ·
        have hc_lt : lx.length < q := lt_of_le_of_ne hlx_le_q hxq'
        set d : ℕ := q - lx.length with hd
        have hdpos : 0 < d := by
          have : 0 < q - lx.length := Nat.sub_pos_of_lt hc_lt
          simpa [hd] using this
        have hd1 : 1 ≤ d := Nat.succ_le_iff.2 hdpos

        have hq_eq : lx.length + d = q := by
          simpa [hd] using (Nat.add_sub_of_le hlx_le_q)

        have hq_mul : q * x = lx.length * x + d * x := by
          have hq_eq' : q = lx.length + d := hq_eq.symm
          calc
            q * x = (lx.length + d) * x := by simpa [hq_eq']
            _ = lx.length * x + d * x := by simpa [Nat.add_mul]

        have hlr_sum_formula : lr.sum = d * x + (x - 1) := by
          have hEq : lx.length * x + lr.sum = q * x + (x - 1) := by
            simpa [hlx_sum, hsum_decomp] using hl_sum
          have hEq2 : lx.length * x + lr.sum = lx.length * x + (d * x + (x - 1)) := by
            calc
              lx.length * x + lr.sum = q * x + (x - 1) := hEq
              _ = (lx.length * x + d * x) + (x - 1) := by
                simpa [hq_mul]
              _ = lx.length * x + (d * x + (x - 1)) := by
                simp [Nat.add_assoc]
          exact Nat.add_left_cancel hEq2

        have hTsucc : doubly_T b (k + 1) = q + doubly_T b k := by
          simpa [hq, hx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (doubly_T_succ b k)

        have hlen_ge : q + doubly_T b k ≤ l.length := by
          cases k with
          | zero =>
              have hx0 : x = b := by
                calc
                  x = doubly_m b 0 := by simpa using hx
                  _ = b := doubly_m_zero b

              have hlr_all1 : ∀ n ∈ lr, n = 1 := by
                intro n hn
                have hn_l : n ∈ l := List.mem_of_mem_filter hn
                have hn_ne : n ≠ x := by
                  have hn_dec : decide (n ≠ x) = true := by
                    simpa [lr] using (List.of_mem_filter (p := fun m : ℕ => decide (m ≠ x)) hn)
                  exact Bool.of_decide_true hn_dec
                rcases hcoin n hn_l with h1 | ⟨j, hj⟩
                · exact h1
                · cases j with
                  | zero =>
                      have : n = x := by
                        -- n = b^(b^0) = b = x
                        simpa [hj, hx0, doubly_m, pow_one] using rfl
                      exact (False.elim (hn_ne this))
                  | succ j =>
                      have hnle : n ≤ l.sum := List.le_sum_of_mem hn_l
                      have hnle' : n ≤ x ^ b - 1 := by
                        simpa [hsum'] using hnle
                      have hExp : b ^ 1 ≤ b ^ (Nat.succ j) := by
                        exact pow_le_pow_right' hb1 (Nat.succ_le_succ (Nat.zero_le j))
                      have hpow : b ^ (b ^ 1) ≤ b ^ (b ^ (Nat.succ j)) := pow_le_pow_right' hb1 hExp
                      have hbpow_le_n : b ^ b ≤ n := by
                        -- rewrite using hj
                        simpa [hj, pow_one] using hpow
                      have hbpow_pos : 0 < b ^ b := pow_pos hbpos b
                      have hlt : b ^ b - 1 < b ^ b := tsub_lt_self hbpow_pos (by decide : (0 : ℕ) < 1)
                      have : b ^ b ≤ b ^ b - 1 := le_trans hbpow_le_n (by
                        -- use hx0 to rewrite x as b
                        simpa [hx0] using hnle')
                      exact (False.elim ((not_le_of_lt hlt) this))

              have hlr_sum_len : lr.sum = lr.length := by
                have h :=
                  List.sum_eq_card_nsmul (l := lr) (m := (1 : ℕ)) (by
                    intro n hn
                    exact hlr_all1 n hn)
                simpa [nsmul_eq_mul] using h

              have hlr_len_formula : lr.length = d * x + (x - 1) := by
                simpa [hlr_sum_formula] using hlr_sum_len.symm

              have hd_le_dmul : d ≤ d * x := by
                have := Nat.mul_le_mul_left d hx1
                simpa [Nat.mul_one] using this

              have hr_le : d + (x - 1) ≤ lr.length := by
                have : d + (x - 1) ≤ d * x + (x - 1) := Nat.add_le_add_right hd_le_dmul (x - 1)
                simpa [hlr_len_formula] using this

              have hlen : lx.length + (d + (x - 1)) ≤ l.length := by
                have : lx.length + (d + (x - 1)) ≤ lx.length + lr.length :=
                  Nat.add_le_add_left hr_le lx.length
                simpa [hl_len] using this

              have hlen2 : (lx.length + d) + (x - 1) ≤ l.length := by
                simpa [Nat.add_assoc] using hlen

              have hlen' : q + (x - 1) ≤ l.length := by
                simpa [hq_eq] using hlen2

              have hT0 : doubly_T b 0 = x - 1 := by
                simpa [hx0, doubly_T_zero] using (doubly_T_zero b)

              simpa [hT0] using hlen'

          | succ k0 =>
              set y : ℕ := doubly_m b k0 with hy

              have hx_y : x = y ^ b := by
                calc
                  x = doubly_m b (Nat.succ k0) := by simpa using hx
                  _ = (doubly_m b k0) ^ b := by simpa using (doubly_m_succ b k0)
                  _ = y ^ b := by simpa [hy]

              have hb_le_y : b ≤ y := by
                have hmono : Monotone (doubly_m b) := doubly_m_mono b hb
                have : doubly_m b 0 ≤ doubly_m b k0 := hmono (Nat.zero_le k0)
                simpa [hy, doubly_m_zero] using this

              have hy2 : 2 ≤ y := le_trans hb hb_le_y
              have hy1 : 1 ≤ y := le_trans (by decide : (1 : ℕ) ≤ 2) hy2
              have hy1lt : 1 < y := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hy2
              have hypos : 0 < y := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hy2

              have hlr_le_y : ∀ n ∈ lr, n ≤ y := by
                intro n hn
                have hn_l : n ∈ l := List.mem_of_mem_filter hn
                have hn_ne : n ≠ x := by
                  have hn_dec : decide (n ≠ x) = true := by
                    simpa [lr] using (List.of_mem_filter (p := fun m : ℕ => decide (m ≠ x)) hn)
                  exact Bool.of_decide_true hn_dec
                have hn_coin : doublyCoin b n := hcoin n hn_l
                have hn_le_sum : n ≤ l.sum := List.le_sum_of_mem hn_l
                have hn_le_mkp1 : n ≤ doubly_m b (Nat.succ (Nat.succ k0)) - 1 := by
                  simpa [hsum] using hn_le_sum
                have hn_le_x : n ≤ x := by
                  have hn_le_mk : n ≤ doubly_m b (Nat.succ k0) :=
                    doublyRep_coin_le_mk b hb hn_coin hn_le_mkp1
                  simpa [hx] using hn_le_mk
                have hn_lt_x : n < x := lt_of_le_of_ne hn_le_x hn_ne
                have hn_le_xsub1 : n ≤ x - 1 := Nat.le_pred_of_lt hn_lt_x
                have hn_le_mk0 : n ≤ doubly_m b k0 := by
                  have : n ≤ doubly_m b (Nat.succ k0) - 1 := by
                    simpa [hx] using hn_le_xsub1
                  exact doublyRep_coin_le_mk b hb hn_coin this
                simpa [hy] using hn_le_mk0

              have hlr_sum_le : lr.sum ≤ lr.length * y := by
                have h := List.sum_le_card_nsmul (l := lr) (n := y) (h := by
                  intro n hn
                  exact hlr_le_y n hn)
                simpa [nsmul_eq_mul] using h

              set A : ℕ := (d + 1) * (y ^ (b - 1)) with hA

              have hApos : 0 < A := by
                have : 0 < y ^ (b - 1) := pow_pos hypos (b - 1)
                simpa [hA] using Nat.mul_pos (Nat.succ_pos d) this

              have hA1 : 1 ≤ A := Nat.succ_le_iff.2 hApos

              have hy_le_Ay : y ≤ A * y := by
                have := Nat.mul_le_mul_right y hA1
                simpa [Nat.one_mul] using this

              have hsub_lt : A * y - y < A * y - 1 := by
                exact tsub_lt_tsub_left_of_le hy_le_Ay hy1lt

              have hy_pow : y ^ b = y ^ (b - 1) * y := by
                have := pow_succ y (b - 1)
                simpa [hb_eq] using this

              have hAy : A * y = (d + 1) * (y ^ b) := by
                calc
                  A * y = ((d + 1) * (y ^ (b - 1))) * y := by
                    simp [hA]
                  _ = (d + 1) * (y ^ (b - 1) * y) := by
                    simp [Nat.mul_assoc]
                  _ = (d + 1) * (y ^ b) := by
                    simp [hy_pow]

              have hyb_pos : 0 < y ^ b := pow_pos hypos b
              have hyb1 : 1 ≤ y ^ b := Nat.succ_le_iff.2 hyb_pos

              have hlr_sum_eq : lr.sum = (d + 1) * (y ^ b) - 1 := by
                have htmp : d * (y ^ b) + y ^ b = (d + 1) * (y ^ b) := by
                  simpa [Nat.succ_eq_add_one] using (Nat.succ_mul d (y ^ b)).symm
                calc
                  lr.sum = d * x + (x - 1) := hlr_sum_formula
                  _ = d * (y ^ b) + (y ^ b - 1) := by
                    simp [hx_y]
                  _ = (d * (y ^ b) + y ^ b) - 1 := by
                    simpa using (Nat.add_sub_assoc hyb1 (d * (y ^ b))).symm
                  _ = (d + 1) * (y ^ b) - 1 := by
                    simpa [htmp]

              have hlr_sum_eq_Ay : lr.sum = A * y - 1 := by
                calc
                  lr.sum = (d + 1) * (y ^ b) - 1 := hlr_sum_eq
                  _ = A * y - 1 := by
                    symm
                    simpa [hAy]

              have hA_le_r : A ≤ lr.length := by
                by_contra hAr
                have hr_lt : lr.length < A := lt_of_not_ge hAr
                have hr_le : lr.length ≤ A - 1 := Nat.le_pred_of_lt hr_lt
                have hmul_le : lr.length * y ≤ A * y - y := by
                  have := Nat.mul_le_mul_right y hr_le
                  simpa [tsub_one_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
                have hlr_sum_le' : lr.sum ≤ A * y - y := le_trans hlr_sum_le hmul_le
                have : A * y - 1 ≤ A * y - y := by
                  simpa [hlr_sum_eq_Ay] using hlr_sum_le'
                exact (not_le_of_lt hsub_lt) this

              have hT_k0_le : doubly_T b k0 ≤ y ^ (b - 1) := by
                have hTle : doubly_T b k0 ≤ doubly_m b k0 - 1 := doubly_T_le_m_sub_one b hb k0
                have hTle' : doubly_T b k0 ≤ y - 1 := by
                  simpa [hy] using hTle
                have hbgt : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
                have hbsub1_ne : b - 1 ≠ 0 := by
                  exact ne_of_gt (Nat.sub_pos_of_lt hbgt)
                have hy_le_pow : y ≤ y ^ (b - 1) := le_self_pow hy1 hbsub1_ne
                have : y - 1 ≤ y ^ (b - 1) := le_trans (Nat.sub_le y 1) hy_le_pow
                exact le_trans hTle' this

              have hT_eq : doubly_T b (Nat.succ k0) = y ^ (b - 1) - 1 + doubly_T b k0 := by
                simpa [hy] using (doubly_T_succ b k0)

              have hTsucc_le : doubly_T b (Nat.succ k0) ≤ y ^ (b - 1) - 1 + y ^ (b - 1) := by
                rw [hT_eq]
                exact Nat.add_le_add_left hT_k0_le (y ^ (b - 1) - 1)

              have hDT_le : d + doubly_T b (Nat.succ k0) ≤ A := by
                have h1 : d + doubly_T b (Nat.succ k0) ≤ d + (y ^ (b - 1) - 1 + y ^ (b - 1)) :=
                  Nat.add_le_add_left hTsucc_le d

                let A0 : ℕ := y ^ (b - 1)
                have hA0_pos : 0 < A0 := by
                  dsimp [A0]
                  exact pow_pos hypos (b - 1)
                have hA0_1 : 1 ≤ A0 := Nat.succ_le_iff.2 hA0_pos
                have hA0_eq : (A0 - 1) + 1 = A0 := Nat.sub_add_cancel hA0_1
                have hmul : A0 - 1 ≤ d * (A0 - 1) := by
                  have := Nat.mul_le_mul_left (A0 - 1) hd1
                  simpa [Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
                have hmul2 : d + (A0 - 1) ≤ d + d * (A0 - 1) := Nat.add_le_add_left hmul d
                have hd_mul : d * A0 = d * (A0 - 1) + d := by
                  calc
                    d * A0 = d * ((A0 - 1) + 1) := by
                      simpa [hA0_eq]
                    _ = d * (A0 - 1) + d * 1 := by
                      simp [Nat.mul_add, Nat.add_assoc]
                    _ = d * (A0 - 1) + d := by
                      simp [Nat.mul_one]
                have h3 : d + (A0 - 1) ≤ d * A0 := by
                  calc
                    d + (A0 - 1) ≤ d + d * (A0 - 1) := hmul2
                    _ = d * (A0 - 1) + d := by
                      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
                    _ = d * A0 := by
                      simpa using hd_mul.symm
                have h4 : d + (A0 - 1) + A0 ≤ d * A0 + A0 := Nat.add_le_add_right h3 A0
                have h5 : d * A0 + A0 = (d + 1) * A0 := by
                  simpa [Nat.succ_eq_add_one] using (Nat.succ_mul d A0).symm
                have h2 : d + (A0 - 1 + A0) ≤ (d + 1) * A0 := by
                  simpa [Nat.add_assoc, h5] using h4
                have h2' : d + (y ^ (b - 1) - 1 + y ^ (b - 1)) ≤ A := by
                  simpa [A0, hA] using h2
                exact le_trans h1 h2'

              have hDT_r : d + doubly_T b (Nat.succ k0) ≤ lr.length := le_trans hDT_le hA_le_r

              have hlen : lx.length + (d + doubly_T b (Nat.succ k0)) ≤ l.length := by
                have : lx.length + (d + doubly_T b (Nat.succ k0)) ≤ lx.length + lr.length :=
                  Nat.add_le_add_left hDT_r lx.length
                simpa [hl_len] using this

              have hlen2 : (lx.length + d) + doubly_T b (Nat.succ k0) ≤ l.length := by
                simpa [Nat.add_assoc] using hlen

              have hlen' : q + doubly_T b (Nat.succ k0) ≤ l.length := by
                simpa [hq_eq] using hlen2

              exact hlen'

        have : doubly_T b (k + 1) ≤ l.length := by
          simpa [hTsucc] using hlen_ge
        exact le_trans this hls

theorem doubly_T_succ_le_two_mul_mpow (b : ℕ) (hb : 2 ≤ b) : ∀ k : ℕ, doubly_T b (k + 1) ≤ 2 * (doubly_m b k) ^ (b - 1) := by
  intro k
  have hmpos : 0 < doubly_m b k := doubly_m_pos b k hb
  have hm1 : 1 ≤ doubly_m b k := by
    exact Nat.succ_le_iff.mpr hmpos
  have hb' : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
  have hb1 : b - 1 ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hb')
  have hm_le_pow : doubly_m b k ≤ (doubly_m b k) ^ (b - 1) := le_self_pow hm1 hb1
  have hm_sub_one_le_pow : doubly_m b k - 1 ≤ (doubly_m b k) ^ (b - 1) := by
    have hm_sub_one_le_m : doubly_m b k - 1 ≤ doubly_m b k := by
      simpa using (tsub_le_self (a := doubly_m b k) (b := 1))
    exact le_trans hm_sub_one_le_m hm_le_pow
  have hTk : doubly_T b k ≤ doubly_m b k - 1 := doubly_T_le_m_sub_one b hb k
  have hTk_pow : doubly_T b k ≤ (doubly_m b k) ^ (b - 1) := le_trans hTk hm_sub_one_le_pow
  rw [doubly_T_succ]
  calc
    (doubly_m b k) ^ (b - 1) - 1 + doubly_T b k ≤ (doubly_m b k) ^ (b - 1) + doubly_T b k := by
      have hsub : (doubly_m b k) ^ (b - 1) - 1 ≤ (doubly_m b k) ^ (b - 1) := by
        simpa using (tsub_le_self (a := (doubly_m b k) ^ (b - 1)) (b := 1))
      exact Nat.add_le_add_right hsub (doubly_T b k)
    _ ≤ (doubly_m b k) ^ (b - 1) + (doubly_m b k) ^ (b - 1) := by
      exact Nat.add_le_add_left hTk_pow ((doubly_m b k) ^ (b - 1))
    _ = 2 * (doubly_m b k) ^ (b - 1) := by
      exact (two_mul ((doubly_m b k) ^ (b - 1))).symm

theorem doublyRep_gap_fails_b2_bound (C₂ : ℝ) (hC₂ : 0 < C₂) (k : ℕ) :
  (16 * C₂ : ℝ) < (k : ℝ) →
  let t := doubly_T 2 (k + 1)
  let m := doubly_m 2 (k + 1)
  let s := 2 * t
  (C₂ * Real.rpow (s : ℝ) (2 : ℝ)) < ((t : ℝ) * (m : ℝ)) := by
  intro hk
  simp at *
  set t : ℕ := doubly_T 2 (k + 1) with ht
  set m : ℕ := doubly_m 2 (k + 1) with hm
  set s : ℕ := 2 * t with hs
  set d : ℕ := doubly_m 2 k with hd

  have hb2 : (2 : ℕ) ≤ 2 := by decide

  have ht_le : t ≤ 2 * d := by
    simpa [t, d] using (doubly_T_succ_le_two_mul_mpow 2 hb2 k)

  have hs_le_nat : s ≤ 4 * d := by
    have h : 2 * t ≤ 2 * (2 * d) := Nat.mul_le_mul_left 2 ht_le
    have hs' : s ≤ 2 * (2 * d) := by
      simpa [hs.symm] using h
    have hmul : 2 * (2 * d) = 4 * d := by
      ring
    simpa [hmul] using hs'

  have hs_le_real : (s : ℝ) ≤ (4 * d : ℝ) := by
    exact_mod_cast hs_le_nat

  have hs_nonneg : 0 ≤ (s : ℝ) := by
    exact_mod_cast (Nat.zero_le s)

  have hs_rpow_le : Real.rpow (s : ℝ) (2 : ℝ) ≤ 16 * (m : ℝ) := by
    have h' : (s : ℝ) ^ (2 : ℝ) ≤ (4 * d : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow hs_nonneg hs_le_real (by positivity : (0 : ℝ) ≤ (2 : ℝ))
    have h'' : (s : ℝ) ^ 2 ≤ (4 * d : ℝ) ^ 2 := by
      simpa [Real.rpow_two] using h'

    have hm_nat : m = d ^ 2 := by
      simpa [m, d, pow_two] using (doubly_m_succ 2 k)

    have hm' : (m : ℝ) = (d : ℝ) ^ 2 := by
      -- cast hm_nat
      -- use `Nat.cast_pow` to simplify the cast
      -- Note: `Nat.cast_pow` expects both sides in a semiring
      --
      -- We can rewrite the cast directly.
      --
      have : (m : ℝ) = (d ^ 2 : ℕ) := by
        exact congrArg (fun n : ℕ => (n : ℝ)) hm_nat
      -- now simplify
      simpa [Nat.cast_pow] using this

    have h4d_sq : (4 * d : ℝ) ^ 2 = 16 * ((d : ℝ) ^ 2) := by
      ring

    have : (s : ℝ) ^ 2 ≤ 16 * ((d : ℝ) ^ 2) := by
      simpa [h4d_sq] using h''

    simpa [Real.rpow_two, hm'.symm] using this

  have hC_mul : C₂ * Real.rpow (s : ℝ) (2 : ℝ) ≤ (16 * C₂) * (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hs_rpow_le (le_of_lt hC₂)
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

  have ht_ge : (k + 1) ≤ t := by
    have := (doubly_T_ge_self_fixed 2 hb2 (k + 1))
    simpa [t] using this

  have hk_lt_t : (k : ℝ) < (t : ℝ) := by
    have hk_lt : (k : ℝ) < (k + 1 : ℝ) := by
      -- k < k+1
      linarith
    have hk1_le : (k + 1 : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast ht_ge
    exact lt_of_lt_of_le hk_lt hk1_le

  have h16C_lt_t : (16 * C₂ : ℝ) < (t : ℝ) := lt_trans hk hk_lt_t

  have hm_pos : 0 < (m : ℝ) := by
    have hm_pos_nat : 0 < m := by
      simp [m, doubly_m]
    exact_mod_cast hm_pos_nat

  have h16C_mul_lt : (16 * C₂ : ℝ) * (m : ℝ) < (t : ℝ) * (m : ℝ) := by
    exact mul_lt_mul_of_pos_right h16C_lt_t hm_pos

  have hC_mul_lt : C₂ * Real.rpow (s : ℝ) (2 : ℝ) < (t : ℝ) * (m : ℝ) := by
    exact lt_of_le_of_lt hC_mul (by simpa [mul_assoc, mul_left_comm, mul_comm] using h16C_mul_lt)

  simpa [Real.rpow_two, hs] using hC_mul_lt


theorem exists_k_T_le_s_lt_T_succ (b s : ℕ) (hb : 2 ≤ b) (hs : b - 1 ≤ s) :
  ∃ k : ℕ, doubly_T b k ≤ s ∧ s < doubly_T b (k + 1) := by
  classical

  have hb1 : 1 ≤ b := by
    exact le_trans (by decide : 1 ≤ 2) hb

  have hbsub : 1 ≤ b - 1 := by
    have h := Nat.sub_le_sub_right hb 1
    -- h : 2 - 1 ≤ b - 1
    simpa using h

  have hm_ge_two : ∀ k : ℕ, 2 ≤ doubly_m b k := by
    intro k
    dsimp [doubly_m]
    have hkexp : 1 ≤ b ^ k := by
      exact one_le_pow₀ hb1
    have hb_le_pow : b ≤ b ^ (b ^ k) := by
      have hpow : b ^ 1 ≤ b ^ (b ^ k) := by
        exact pow_le_pow_right' hb1 hkexp
      simpa using hpow
    exact le_trans hb hb_le_pow

  have hstep : ∀ k : ℕ, doubly_T b k + 1 ≤ doubly_T b (k + 1) := by
    intro k
    have hm2 : 2 ≤ doubly_m b k := hm_ge_two k
    have hm1 : 1 ≤ doubly_m b k := le_trans (by decide : 1 ≤ 2) hm2

    have hpow_ge_two : 2 ≤ (doubly_m b k) ^ (b - 1) := by
      have hm_le_pow : doubly_m b k ≤ (doubly_m b k) ^ (b - 1) := by
        have hpow : (doubly_m b k) ^ 1 ≤ (doubly_m b k) ^ (b - 1) := by
          exact pow_le_pow_right' hm1 hbsub
        simpa using hpow
      exact le_trans hm2 hm_le_pow

    have hsub1 : 1 ≤ (doubly_m b k) ^ (b - 1) - 1 := by
      have h := Nat.sub_le_sub_right hpow_ge_two 1
      simpa using h

    have hadd : 1 + doubly_T b k ≤ (doubly_m b k) ^ (b - 1) - 1 + doubly_T b k :=
      Nat.add_le_add_right hsub1 (doubly_T b k)

    -- rewrite `doubly_T` and commute `+ 1`
    rw [doubly_T_succ]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hadd

  have hge : ∀ n : ℕ, n ≤ doubly_T b n := by
    intro n
    induction n with
    | zero =>
        exact Nat.zero_le _
    | succ n ih =>
        have h1 : n + 1 ≤ doubly_T b n + 1 := Nat.add_le_add_right ih 1
        have h2 : doubly_T b n + 1 ≤ doubly_T b (n + 1) := hstep n
        exact le_trans h1 h2

  have hex : ∃ k : ℕ, s < doubly_T b k := by
    refine ⟨s + 1, ?_⟩
    have hs1 : s < s + 1 := Nat.lt_succ_self s
    have hle : s + 1 ≤ doubly_T b (s + 1) := hge (s + 1)
    exact lt_of_lt_of_le hs1 hle

  let k0 : ℕ := Nat.find hex
  have hk0spec : s < doubly_T b k0 := Nat.find_spec hex

  have hT0le : doubly_T b 0 ≤ s := by
    simpa [doubly_T_zero] using hs

  have hk0ne : k0 ≠ 0 := by
    intro hk0zero
    have hlt : s < doubly_T b 0 := by
      simpa [hk0zero] using hk0spec
    exact (not_lt_of_ge hT0le) hlt

  have hk0pos : 0 < k0 := Nat.pos_of_ne_zero hk0ne
  have hk0one : 1 ≤ k0 := by
    -- `1 ≤ k0` is the same as `0 < k0`
    simpa using (Nat.succ_le_iff.2 hk0pos)

  refine ⟨k0 - 1, ?_, ?_⟩
  · have hklt : k0 - 1 < k0 := by
      omega
    have hnot : ¬ s < doubly_T b (k0 - 1) := Nat.find_min hex hklt
    exact le_of_not_gt hnot
  · -- `k0 - 1 + 1 = k0`
    simpa [Nat.sub_add_cancel hk0one] using hk0spec

theorem fa1_eq_replicate_card (m : FreeAbelianMonoid 1) : m = Multiset.replicate m.card (0 : Fin 1) := by
  classical
  induction m using Multiset.induction_on with
  | empty =>
      -- m = 0
      simp [Multiset.card_zero]
  | @cons a t ih =>
      have ha : a = (0 : Fin 1) := Subsingleton.elim a 0
      subst ha
      -- rewrite the goal using the cardinality of `cons`
      rw [Multiset.card_cons]
      -- now use the induction hypothesis and `replicate_succ`
      have h1 : (0 : Fin 1) ::ₘ t = (0 : Fin 1) ::ₘ Multiset.replicate t.card (0 : Fin 1) :=
        congrArg (fun s => (0 : Fin 1) ::ₘ s) ih
      have h2 :
          (0 : Fin 1) ::ₘ Multiset.replicate t.card (0 : Fin 1) =
            Multiset.replicate (t.card + 1) (0 : Fin 1) :=
        (Multiset.replicate_succ (a := (0 : Fin 1)) (n := t.card)).symm
      exact h1.trans h2

theorem loglog_bpowb_eq (b : ℕ) (hb : 2 ≤ b) :
  Real.log (Real.log (b ^ b)) = Real.log b + Real.log (Real.log b) := by
  -- Rewrite the inner log using `Real.log_pow` and then apply `Real.log_mul`
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    -- from `2 ≤ b` we get `1 < b`, then cast to ℝ
    have hbNat : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    exact_mod_cast hbNat

  have hb0 : (b : ℝ) ≠ 0 := by
    -- b ≥ 2 so b ≠ 0
    have hbNat0 : (b : ℕ) ≠ 0 := by
      have : (0 : ℕ) < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
      exact ne_of_gt this
    -- cast to ℝ
    exact_mod_cast hbNat0

  have hlogb0 : Real.log (b : ℝ) ≠ 0 := by
    -- since b > 1, log b > 0
    have : 0 < Real.log (b : ℝ) := Real.log_pos hb1
    exact ne_of_gt this

  -- compute log (b^b)
  have h1 : Real.log (Real.log (b ^ b)) = Real.log (Real.log ((b : ℝ) ^ b)) := by
    -- rewrite (b^b : ℝ) as (b:ℝ)^b
    -- note: both sides are definitional equalities after rewriting inside
    simp only [Nat.cast_pow]

  -- now use log_pow
  have h2 : Real.log ((b : ℝ) ^ b) = (b : ℝ) * Real.log (b : ℝ) := by
    -- `Real.log_pow` gives `b * log b`; rewrite `b` as `(b:ℝ)`
    simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.log_pow (b : ℝ) b)

  -- finish
  -- rewrite the inner log as `log (b * log b)` and apply `Real.log_mul`
  calc
    Real.log (Real.log (b ^ b))
        = Real.log (Real.log ((b : ℝ) ^ b)) := by
            -- cast and rewrite
            simp only [Nat.cast_pow]
    _   = Real.log ((b : ℝ) * Real.log (b : ℝ)) := by
            -- use log_pow
            simp only [h2]
    _   = Real.log (b : ℝ) + Real.log (Real.log (b : ℝ)) := by
            -- log of product
            simpa [mul_assoc] using (Real.log_mul hb0 hlogb0)
    _   = Real.log b + Real.log (Real.log b) := by
            norm_cast


theorem loglog_pos_of_ge_bpowb (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) : 0 < Real.log (Real.log x) := by
  -- We show `1 < Real.log x`, then use `Real.log_pos`.
  have hb1 : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have h4bb : (4 : ℕ) ≤ b ^ b := by
    have h : (2 : ℕ) ^ 2 ≤ b ^ b := pow_le_pow hb hb1 hb
    have h2 : (2 : ℕ) ^ 2 = 4 := by norm_num
    simpa [h2] using h
  have hx4 : (4 : ℕ) ≤ x := le_trans h4bb hx
  have hx4R : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4
  have hexp4 : Real.exp (1 : ℝ) < (4 : ℝ) := by
    have h : Real.exp (1 : ℝ) < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have h2 : (2.7182818286 : ℝ) < (4 : ℝ) := by norm_num
    exact lt_trans h h2
  have hexpX : Real.exp (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le hexp4 hx4R
  have hxpos : (0 : ℝ) < (x : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (4 : ℝ)) hx4R
  have h1logx : (1 : ℝ) < Real.log (x : ℝ) :=
    (Real.lt_log_iff_exp_lt hxpos).2 hexpX
  -- Now `log (log x) > 0` since `log x > 1`.
  exact Real.log_pos (by simpa using h1logx)

theorem loglog_mono_ge_bpowb (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) :
  Real.log (Real.log (b ^ b)) ≤ Real.log (Real.log x) := by
  have hx' : (b ^ b : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hx
  have hbb_pos : (0 : ℝ) < (b ^ b : ℝ) := by
    positivity
  have hlog_le : Real.log (b ^ b : ℝ) ≤ Real.log (x : ℝ) := by
    exact Real.log_le_log hbb_pos hx'
  have hb1 : 1 < b := by
    exact lt_of_lt_of_le (by decide : 1 < 2) hb
  have hb0 : b ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hb)
  have hbb_gt1_nat : 1 < b ^ b := by
    exact Nat.one_lt_pow hb0 hb1
  have hbb_gt1 : (1 : ℝ) < (b ^ b : ℝ) := by
    exact_mod_cast hbb_gt1_nat
  have hlogbb_pos : 0 < Real.log (b ^ b : ℝ) := by
    exact Real.log_pos hbb_gt1
  have hloglog_le : Real.log (Real.log (b ^ b : ℝ)) ≤ Real.log (Real.log (x : ℝ)) := by
    exact Real.log_le_log hlogbb_pos hlog_le
  simpa using hloglog_le

theorem loglogb_le_half_loglog_of_ge_bpowb (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) :
  Real.log (Real.log b) ≤ (1 / 2 : ℝ) * Real.log (Real.log x) := by
  have hsum : Real.log b + Real.log (Real.log b) ≤ Real.log (Real.log x) := by
    have h := loglog_mono_ge_bpowb b x hb hx
    rw [loglog_bpowb_eq b hb] at h
    exact h
  have hlogb_nonneg : (0 : ℝ) ≤ Real.log b := by
    simpa using Real.log_natCast_nonneg b
  have hloglog_le_log : Real.log (Real.log b) ≤ Real.log b := by
    exact Real.log_le_self hlogb_nonneg
  have hdouble : (2 : ℝ) * Real.log (Real.log b) ≤ Real.log b + Real.log (Real.log b) := by
    linarith [hloglog_le_log]
  have hfinal : (2 : ℝ) * Real.log (Real.log b) ≤ Real.log (Real.log x) :=
    le_trans hdouble hsum
  linarith [hfinal]

theorem nat_two_mul_sub_self (t : ℕ) : 2 * t - t = t := by
  calc
    2 * t - t = (t + t) - t := by
      simp [two_mul]
    _ = t := by
      simpa using Nat.add_sub_cancel t t


theorem nat_sub_two_mul_add_one (t : ℕ) : 2 * t - t + 1 = t + 1 := by
  simp [nat_two_mul_sub_self]

theorem natlog_natlog_pow_sandwich (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) :
  let k : ℕ := Nat.log b (Nat.log b x)
  b ^ (b ^ k) ≤ x ∧ x < b ^ (b ^ (k + 1)) := by
  classical
  dsimp
  set y : ℕ := Nat.log b x with hy
  set k : ℕ := Nat.log b y with hk

  have hb1 : 1 < b := by
    omega
  have hb1le : 1 ≤ b := by
    omega
  have hb0 : 0 < b := by
    omega
  have hbne0 : b ≠ 0 := Nat.ne_of_gt hb0

  have hb_le_pow : b ≤ b ^ b := le_self_pow hb1le hbne0
  have hbx : b ≤ x := le_trans hb_le_pow hx

  have hxpos : 0 < x := lt_of_lt_of_le (Nat.pow_pos (n := b) hb0) hx
  have hxne0 : x ≠ 0 := Nat.ne_of_gt hxpos

  have hypos : 0 < y := by
    have : 0 < Nat.log b x := Nat.log_pos hb1 hbx
    simpa [hy] using this
  have hyne0 : y ≠ 0 := Nat.ne_of_gt hypos

  have hbk_le_y : b ^ k ≤ y := by
    have : b ^ Nat.log b y ≤ y := Nat.pow_log_le_self b hyne0
    simpa [hk] using this

  have hby_le_x : b ^ y ≤ x := by
    have : b ^ Nat.log b x ≤ x := Nat.pow_log_le_self b hxne0
    simpa [hy] using this

  have hleft : b ^ (b ^ k) ≤ x := by
    have : b ^ (b ^ k) ≤ b ^ y := pow_le_pow_right' hb1le hbk_le_y
    exact le_trans this hby_le_x

  have hy_lt : y < b ^ (k + 1) := by
    have hy_lt0 : y < b ^ (Nat.log b y).succ := Nat.lt_pow_succ_log_self hb1 y
    have hy_lt1 : y < b ^ (Nat.log b y + 1) := by
      simpa [Nat.succ_eq_add_one] using hy_lt0
    simpa [hk] using hy_lt1

  have hx_lt : x < b ^ y.succ := by
    have : x < b ^ (Nat.log b x).succ := Nat.lt_pow_succ_log_self hb1 x
    simpa [hy] using this

  have hy_succ_le : y.succ ≤ b ^ (k + 1) := Nat.succ_le_of_lt hy_lt

  have hpow : b ^ y.succ ≤ b ^ (b ^ (k + 1)) := pow_le_pow_right' hb1le hy_succ_le

  have hright : x < b ^ (b ^ (k + 1)) := lt_of_lt_of_le hx_lt hpow

  exact ⟨hleft, hright⟩

theorem natlog_natlog_real_loglog_sandwich (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) :
  let k : ℕ := Nat.log b (Nat.log b x)
  ((b ^ k : ℕ) : ℝ) * Real.log b ≤ Real.log x ∧
    Real.log x < ((b ^ (k + 1) : ℕ) : ℝ) * Real.log b := by
  classical
  let k : ℕ := Nat.log b (Nat.log b x)
  have hkNat : b ^ (b ^ k) ≤ x ∧ x < b ^ (b ^ (k + 1)) := by
    simpa [k] using natlog_natlog_pow_sandwich b x hb hx
  have hbposNat : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hbpos : (0 : ℝ) < b := by
    exact_mod_cast hbposNat
  have hxposNat : 0 < x := by
    exact lt_of_lt_of_le (pow_pos hbposNat b) hx
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast hxposNat
  have hlower : ((b ^ k : ℕ) : ℝ) * Real.log b ≤ Real.log x := by
    have hpow : ((b : ℝ) ^ (b ^ k)) ≤ (x : ℝ) := by
      have hpow' : ((b ^ (b ^ k) : ℕ) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast hkNat.1
      simpa [Nat.cast_pow] using hpow'
    have h := Real.le_log_of_pow_le hbpos hpow
    simpa using h
  have hupper : Real.log x < ((b ^ (k + 1) : ℕ) : ℝ) * Real.log b := by
    have hlt : (x : ℝ) < (b : ℝ) ^ (b ^ (k + 1)) := by
      have hlt' : ((x : ℕ) : ℝ) < ((b ^ (b ^ (k + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hkNat.2
      simpa [Nat.cast_pow] using hlt'
    have hloglt : Real.log (x : ℝ) < Real.log ((b : ℝ) ^ (b ^ (k + 1))) :=
      Real.log_lt_log hxpos hlt
    simpa [Real.log_pow] using hloglt
  have h : ((b ^ k : ℕ) : ℝ) * Real.log b ≤ Real.log x ∧
      Real.log x < ((b ^ (k + 1) : ℕ) : ℝ) * Real.log b := by
    exact ⟨hlower, hupper⟩
  simpa [k] using h

theorem natlog_natlog_real_loglog_bounds (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) :
  let k : ℕ := Nat.log b (Nat.log b x)
  (k : ℝ) * Real.log b + Real.log (Real.log b) ≤ Real.log (Real.log x) ∧
    Real.log (Real.log x) < ((k + 1 : ℕ) : ℝ) * Real.log b + Real.log (Real.log b) := by
  classical
  dsimp
  set k : ℕ := Nat.log b (Nat.log b x) with hk
  have hsand : ((b ^ k : ℕ) : ℝ) * Real.log (b : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) < ((b ^ (k + 1) : ℕ) : ℝ) * Real.log (b : ℝ) := by
    simpa [k, hk] using natlog_natlog_real_loglog_sandwich b x hb hx
  have hlow : ((b ^ k : ℕ) : ℝ) * Real.log (b : ℝ) ≤ Real.log (x : ℝ) := hsand.1
  have hupp : Real.log (x : ℝ) < ((b ^ (k + 1) : ℕ) : ℝ) * Real.log (b : ℝ) := hsand.2

  have hb1_nat : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb1_nat
  have hlogbpos : 0 < Real.log (b : ℝ) := Real.log_pos hb1

  have hbpos_nat : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
  have hbpowpos_nat : 0 < b ^ k := pow_pos hbpos_nat k
  have hbpowpos : (0 : ℝ) < ((b ^ k : ℕ) : ℝ) := by
    exact_mod_cast hbpowpos_nat

  have hlowpos : 0 < ((b ^ k : ℕ) : ℝ) * Real.log (b : ℝ) := by
    simpa using (mul_pos hbpowpos hlogbpos)

  have hlogxpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le hlowpos (by simpa using hlow)

  have hlog_le : Real.log (((b ^ k : ℕ) : ℝ) * Real.log (b : ℝ)) ≤ Real.log (Real.log (x : ℝ)) :=
    Real.log_le_log hlowpos (by simpa using hlow)
  have hlog_lt : Real.log (Real.log (x : ℝ)) < Real.log (((b ^ (k + 1) : ℕ) : ℝ) * Real.log (b : ℝ)) :=
    Real.log_lt_log hlogxpos (by simpa using hupp)

  have hbpowne : ((b ^ k : ℕ) : ℝ) ≠ 0 := ne_of_gt hbpowpos
  have hlogbne : Real.log (b : ℝ) ≠ 0 := ne_of_gt hlogbpos

  have hbpow_cast : ((b ^ k : ℕ) : ℝ) = (b : ℝ) ^ k := by
    norm_cast

  have hleft_eq :
      Real.log ((b : ℝ) ^ k * Real.log (b : ℝ)) =
        (k : ℝ) * Real.log (b : ℝ) + Real.log (Real.log (b : ℝ)) := by
    -- start from log of cast-pow product and rewrite
    have h0 :
        Real.log (((b ^ k : ℕ) : ℝ) * Real.log (b : ℝ)) =
          (k : ℝ) * Real.log (b : ℝ) + Real.log (Real.log (b : ℝ)) := by
      calc
        Real.log (((b ^ k : ℕ) : ℝ) * Real.log (b : ℝ))
            = Real.log ((b ^ k : ℕ) : ℝ) + Real.log (Real.log (b : ℝ)) := by
                simpa using (Real.log_mul hbpowne hlogbne)
        _ = Real.log ((b : ℝ) ^ k) + Real.log (Real.log (b : ℝ)) := by
                simpa [hbpow_cast]
        _ = (k : ℝ) * Real.log (b : ℝ) + Real.log (Real.log (b : ℝ)) := by
                simp [Real.log_pow, add_comm, add_left_comm, add_assoc]
    -- rewrite h0 using hbpow_cast
    simpa [hbpow_cast] using h0

  have hbpowpos_succ_nat : 0 < b ^ (k + 1) := pow_pos hbpos_nat (k + 1)
  have hbpowpos_succ : (0 : ℝ) < ((b ^ (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast hbpowpos_succ_nat
  have hbpowne_succ : ((b ^ (k + 1) : ℕ) : ℝ) ≠ 0 := ne_of_gt hbpowpos_succ

  have hbpow_cast_succ : ((b ^ (k + 1) : ℕ) : ℝ) = (b : ℝ) ^ (k + 1) := by
    norm_cast

  have hright_eq :
      Real.log ((b : ℝ) ^ (k + 1) * Real.log (b : ℝ)) =
        ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) + Real.log (Real.log (b : ℝ)) := by
    have h0 :
        Real.log (((b ^ (k + 1) : ℕ) : ℝ) * Real.log (b : ℝ)) =
          ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) + Real.log (Real.log (b : ℝ)) := by
      calc
        Real.log (((b ^ (k + 1) : ℕ) : ℝ) * Real.log (b : ℝ))
            = Real.log ((b ^ (k + 1) : ℕ) : ℝ) + Real.log (Real.log (b : ℝ)) := by
                simpa using (Real.log_mul hbpowne_succ hlogbne)
        _ = Real.log ((b : ℝ) ^ (k + 1)) + Real.log (Real.log (b : ℝ)) := by
                simpa [hbpow_cast_succ]
        _ = ((k + 1 : ℕ) : ℝ) * Real.log (b : ℝ) + Real.log (Real.log (b : ℝ)) := by
                simp [Real.log_pow, add_comm, add_left_comm, add_assoc]
    simpa [hbpow_cast_succ] using h0

  have hlog_le' : Real.log ((b : ℝ) ^ k * Real.log (b : ℝ)) ≤ Real.log (Real.log (x : ℝ)) := by
    simpa [hbpow_cast] using hlog_le

  have hlog_lt' : Real.log (Real.log (x : ℝ)) < Real.log ((b : ℝ) ^ (k + 1) * Real.log (b : ℝ)) := by
    simpa [hbpow_cast_succ] using hlog_lt

  constructor
  ·
    simpa [hleft_eq] using hlog_le'
  ·
    simpa [hright_eq] using hlog_lt'

theorem natlog_natlog_doublelog_lower_explicit (b : ℕ) (hb : 2 ≤ b) :
  ∀ (x : ℕ), x ≥ b ^ b →
    (1 / (2 * Real.log b)) * Real.log (Real.log x) ≤ (Nat.log b (Nat.log b x) + 1 : ℕ) := by
  intro x hx
  classical
  set k : ℕ := Nat.log b (Nat.log b x) with hk
  have hbounds : (k : ℝ) * Real.log b + Real.log (Real.log b) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) < ((k + 1 : ℕ) : ℝ) * Real.log b + Real.log (Real.log b) := by
    simpa [k] using natlog_natlog_real_loglog_bounds b x hb hx
  have hupper : Real.log (Real.log x) < ((k + 1 : ℕ) : ℝ) * Real.log b + Real.log (Real.log b) :=
    hbounds.2
  have hloglogb_le : Real.log (Real.log b) ≤ (1 / 2 : ℝ) * Real.log (Real.log x) :=
    loglogb_le_half_loglog_of_ge_bpowb b x hb hx
  have hsub : Real.log (Real.log x) - Real.log (Real.log b) < ((k + 1 : ℕ) : ℝ) * Real.log b := by
    exact (sub_lt_iff_lt_add).2 (by simpa [add_assoc, add_comm, add_left_comm] using hupper)
  have hhalf_le : (1 / 2 : ℝ) * Real.log (Real.log x) ≤
      Real.log (Real.log x) - Real.log (Real.log b) := by
    linarith [hloglogb_le]
  have hhalf_lt : (1 / 2 : ℝ) * Real.log (Real.log x) < ((k + 1 : ℕ) : ℝ) * Real.log b :=
    lt_of_le_of_lt hhalf_le hsub
  -- show `0 < Real.log b`
  have hb1 : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have hb1r : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb1
  have hlogbpos : 0 < Real.log b := Real.log_pos hb1r
  -- multiply `hhalf_lt` by 2 to remove the `1/2`
  have hmul2 : Real.log (Real.log x) < ((k + 1 : ℕ) : ℝ) * (2 * Real.log b) := by
    have h2pos : (0 : ℝ) < (2 : ℝ) := by
      norm_num
    have := (mul_lt_mul_of_pos_left hhalf_lt h2pos)
    -- simplify
    -- `2 * (1/2) = 1`
    simpa [mul_assoc, mul_left_comm, mul_comm, two_mul] using this
  have hdenpos : 0 < (2 * Real.log b) := by
    nlinarith
  have hdiv : Real.log (Real.log x) / (2 * Real.log b) < ((k + 1 : ℕ) : ℝ) := by
    -- use `div_lt_iff₀`
    exact (div_lt_iff₀ hdenpos).2 (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul2)
  -- rewrite target LHS and finish
  have hdiv' : (1 / (2 * Real.log b)) * Real.log (Real.log x) < ((k + 1 : ℕ) : ℝ) := by
    -- `a / b = a * (1/b)`
    -- and commutativity lets us match
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
  exact le_of_lt hdiv'

theorem neg_loglogb_le_logb (b : ℕ) (hb : 2 ≤ b) :
  - Real.log (Real.log b) ≤ Real.log b := by
  have hpos' : 0 < Real.log (Real.log (↑(b ^ b) : Real)) :=
    loglog_pos_of_ge_bpowb b (b ^ b) hb (le_rfl)
  have hpos : 0 < Real.log (Real.log (↑b ^ b)) := by
    simpa only [Nat.cast_pow] using hpos'
  have hsum : 0 < Real.log b + Real.log (Real.log b) := by
    simpa only [loglog_bpowb_eq b hb] using hpos
  have hlt : -Real.log (Real.log b) < Real.log b := by
    have h1 := add_lt_add_right hsum (-Real.log (Real.log b))
    simpa [add_assoc] using h1
  exact le_of_lt hlt

theorem one_add_int_floor_toNat_lt_of_lt (x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hxn : x < (n : ℝ)) : 1 + Int.toNat (Int.floor x) < n + 1 := by
  have hfloor : Nat.floor x < n := (Nat.floor_lt hx).2 hxn
  have h' : Nat.floor x + 1 < n + 1 := Nat.add_lt_add_right hfloor 1
  simpa [Int.floor_toNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'

theorem doublyRep_gap_fails_b2 (C₂ B : ℝ) (hC₂ : 0 < C₂) :
  ∃ s : ℕ, (s : ℝ) ≥ B ∧
    (∀ N : ℕ,
      N ≤ 1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ))) →
        doublyRep 2 s N) := by
  classical
  let R : ℝ := max (B / 2) (16 * C₂)
  obtain ⟨k : ℕ, hk : R < (k : ℝ)⟩ := exists_nat_gt R
  have hkB : B / 2 < (k : ℝ) :=
    lt_of_le_of_lt (le_max_left (B / 2) (16 * C₂)) hk
  have hk16 : (16 * C₂ : ℝ) < (k : ℝ) :=
    lt_of_le_of_lt (le_max_right (B / 2) (16 * C₂)) hk
  let t : ℕ := doubly_T 2 (k + 1)
  let m : ℕ := doubly_m 2 (k + 1)
  let s : ℕ := 2 * t
  refine ⟨s, ?_, ?_⟩
  · -- show (s : ℝ) ≥ B
    have hb2 : (2 : ℕ) ≤ 2 := by decide
    have ht_ge : k + 1 ≤ t := by
      simpa [t] using (doubly_T_ge_self_fixed 2 hb2 (k + 1))
    have hs_ge_nat : 2 * (k + 1) ≤ s := by
      dsimp [s]
      exact Nat.mul_le_mul_left 2 ht_ge
    have hB_lt_2k : B < 2 * (k : ℝ) := by
      nlinarith
    have hklt : (k : ℝ) < (k + 1 : ℝ) := by
      exact_mod_cast (Nat.lt_succ_self k)
    have h2k_lt_2k1 : 2 * (k : ℝ) < 2 * (k + 1 : ℝ) := by
      nlinarith
    have hB_lt_2k1 : B < 2 * (k + 1 : ℝ) := lt_trans hB_lt_2k h2k_lt_2k1
    have h2k1_le_s : (2 * (k + 1 : ℝ)) ≤ (s : ℝ) := by
      exact_mod_cast hs_ge_nat
    have hB_lt_s : B < (s : ℝ) := lt_of_lt_of_le hB_lt_2k1 h2k1_le_s
    exact le_of_lt hB_lt_s
  · intro N hN
    have hb2 : (2 : ℕ) ≤ 2 := by decide
    have hTle : doubly_T 2 (k + 1) ≤ s := by
      -- t ≤ 2 * t
      dsimp [s, t]
      exact Nat.le_mul_of_pos_left _ (by decide : 0 < (2 : ℕ))
    have hgap : (C₂ * Real.rpow (s : ℝ) (2 : ℝ)) < ((t : ℝ) * (m : ℝ)) := by
      simpa [t, m, s] using (doublyRep_gap_fails_b2_bound C₂ hC₂ k hk16)
    have hx0 : 0 ≤ (C₂ * Real.rpow (s : ℝ) (2 : ℝ)) := by
      have hC₂0 : 0 ≤ C₂ := le_of_lt hC₂
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast (Nat.zero_le s)
      exact mul_nonneg hC₂0 (Real.rpow_nonneg hs0 _)
    have hgap' : (C₂ * Real.rpow (s : ℝ) (2 : ℝ)) < ((t * m : ℕ) : ℝ) := by
      -- convert RHS
      simpa [Nat.cast_mul] using hgap
    have hfloor_lt : 1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ))) < t * m + 1 := by
      simpa using
        (one_add_int_floor_toNat_lt_of_lt (C₂ * Real.rpow (s : ℝ) (2 : ℝ)) (t * m) hx0 hgap')
    have htm1_le : t * m + 1 ≤ (t + 1) * m := by
      -- arithmetic in ℕ
      nlinarith
    have hfloor_lt' :
        1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ))) < (t + 1) * m :=
      lt_of_lt_of_le hfloor_lt htm1_le
    have hNlt : N < (t + 1) * m :=
      lt_of_le_of_lt hN hfloor_lt'
    have hs_sub : s - doubly_T 2 (k + 1) + 1 = t + 1 := by
      dsimp [s, t]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (nat_sub_two_mul_add_one (doubly_T 2 (k + 1)))
    have hNlt' : N < (s - doubly_T 2 (k + 1) + 1) * doubly_m 2 (k + 1) := by
      simpa [hs_sub, t, m] using hNlt
    exact doublyRep_cover_affine 2 hb2 (k + 1) s N hTle hNlt'

theorem not_doublyRep_growth_claim_b2 (hb2 : 2 ≤ (2 : ℕ)) :
  ¬ (∃ C₁ C₂ B : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧
      (∀ (s : ℕ), (s : ℝ) ≥ B →
        let rs := Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1))
        ((∀ N : ℕ, N ≤ Int.toNat (Int.ceil (C₁ * rs)) → doublyRep 2 s N)
          ∧ (∃ N : ℕ, N ≤ 1 + Int.toNat (Int.floor (C₂ * rs)) ∧ ¬ doublyRep 2 s N)))) := by
  rintro ⟨C₁, C₂, B, hC₁, hC₂, hforall⟩
  rcases doublyRep_gap_fails_b2 C₂ B hC₂ with ⟨s, hsB, hrepAll⟩
  have hspec := hforall s hsB
  dsimp at hspec
  rcases hspec with ⟨-, ⟨N, hNle, hNnot⟩⟩
  have hexp : ((2 : ℝ) / (2 - 1)) = (2 : ℝ) := by
    norm_num
  have hNle' : N ≤ 1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ))) := by
    simpa [hexp] using hNle
  have hRep : doublyRep 2 s N := hrepAll N hNle'
  exact hNnot hRep

theorem replicate_mem_ball_doublyMacro_union_A1_iff (b s N : ℕ) :
  Multiset.replicate N (0 : Fin 1) ∈ Ball s (DoublyMacroSet b ∪ A 1) ↔
    ∃ l : List ℕ,
      l.length ≤ s ∧
        (∀ n ∈ l, n = 1 ∨ ∃ j : ℕ, n = b ^ (b ^ j)) ∧
        l.sum = N := by
  classical
  simp [abelian.Ball]
  constructor
  · rintro ⟨L, hLlen, hLX, hLsum⟩
    let l : List ℕ := L.map Multiset.card
    refine ⟨l, ?_, ?_, ?_⟩
    · simpa [l] using hLlen
    · intro n hn
      rcases List.mem_map.1 hn with ⟨m, hmL, rfl⟩
      have hmX : m ∈ DoublyMacroSet b ∨ m ∈ A 1 := hLX m hmL
      rcases hmX with hmD | hmA
      · rcases hmD with ⟨i, j, rfl⟩
        right
        refine ⟨j, ?_⟩
        simp
      · rcases hmA with ⟨i, rfl⟩
        left
        simp
    ·
      have hcard : (L.sum).card = (Multiset.replicate N (0 : Fin 1)).card :=
        congrArg (fun m : Multiset (Fin 1) => m.card) hLsum
      have hsum_cards : (L.sum).card = l.sum := by
        simpa [l] using (Multiset.cardHom (α := Fin 1)).map_list_sum L
      have hrep : (Multiset.replicate N (0 : Fin 1)).card = N := by
        simp
      calc
        l.sum = (L.sum).card := by simpa using hsum_cards.symm
        _ = (Multiset.replicate N (0 : Fin 1)).card := hcard
        _ = N := hrep
  · rintro ⟨l, hl_len, hl_prop, hl_sum⟩
    let L : List (Multiset (Fin 1)) := l.map (fun n => Multiset.replicate n (0 : Fin 1))
    refine ⟨L, ?_, ?_, ?_⟩
    · simpa [L] using hl_len
    · intro m hmL
      rcases List.mem_map.1 hmL with ⟨n, hnL, rfl⟩
      have hnprop : n = 1 ∨ ∃ j : ℕ, n = b ^ (b ^ j) := hl_prop n hnL
      rcases hnprop with hn1 | hnmacro
      · right
        subst hn1
        refine ⟨(0 : Fin 1), ?_⟩
        simp
      · left
        rcases hnmacro with ⟨j, rfl⟩
        refine ⟨(0 : Fin 1), j, ?_⟩
        simp
    ·
      have hcards' : (L.sum).card = (L.map (fun m : Multiset (Fin 1) => m.card)).sum := by
        simpa using (Multiset.cardHom (α := Fin 1)).map_list_sum L
      have hmap : L.map (fun m : Multiset (Fin 1) => m.card) = l := by
        -- this is a purely computational lemma; clear the side conditions
        clear hl_len hl_prop hl_sum hcards'
        dsimp [L]
        induction l with
        | nil =>
            simp
        | cons n l ih =>
            simp [Function.comp, ih, Multiset.card_replicate]
      have hcards : (L.sum).card = l.sum := by
        simpa [hmap] using hcards'
      have hcard_sum : (L.sum).card = N := by
        simpa [hl_sum] using hcards
      calc
        L.sum = Multiset.replicate (L.sum).card (0 : Fin 1) := fa1_eq_replicate_card (L.sum)
        _ = Multiset.replicate N (0 : Fin 1) := by simpa [hcard_sum]


theorem replicate_mem_ball_doublyRep_iff (b s N : ℕ) :
  Multiset.replicate N (0 : Fin 1) ∈ Ball s (DoublyMacroSet b ∪ A 1) ↔ doublyRep b s N := by
  simpa [doublyRep, doublyCoin] using (replicate_mem_ball_doublyMacro_union_A1_iff b s N)


theorem test_nat_real_ge_coe (s : ℕ) (B : ℝ) : (s ≥ B) ↔ ((s : ℝ) ≥ B) := by
  exact Iff.rfl


open abelian in
theorem theorem5_expansion_false_b2 (C₂ B : ℝ) (hC₂ : 0 < C₂) :
  ∃ s : ℕ, (s : ℝ) ≥ B ∧
    (Ball (1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ)))) (A 1) ⊆
      Ball s (DoublyMacroSet 2 ∪ (A 1))) := by
  classical
  rcases doublyRep_gap_fails_b2 C₂ B hC₂ with ⟨s, hsB, hrep⟩
  refine ⟨s, hsB, ?_⟩
  intro m hm
  have hcard : m.card ≤ 1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ))) :=
    (ball_A1_iff_card_le (1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ)))) m).1 hm
  have hmrep : Multiset.replicate m.card (0 : Fin 1) ∈
      Ball s (DoublyMacroSet 2 ∪ A 1) :=
    (replicate_mem_ball_doublyRep_iff 2 s m.card).2 (hrep m.card hcard)
  -- transport hmrep across the equality m = replicate m.card (0)
  exact (fa1_eq_replicate_card m).symm ▸ hmrep

theorem theorem5_expansion_not_b2: ¬ (∃ C₁ C₂ B : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧
      (∀ (s : ℕ), (s : ℝ) ≥ B →
        let rs := Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1))
        (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆
            Ball s (DoublyMacroSet 2 ∪ (A 1))) ∧
          ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs) (A 1) ⊆
              Ball s (DoublyMacroSet 2 ∪ (A 1))))) := by
  intro h
  rcases h with ⟨C₁, C₂, B, hC₁, hC₂, hprop⟩
  rcases theorem5_expansion_false_b2 C₂ B hC₂ with ⟨s, hsB, hscontain⟩
  have hspec :
      (Ball (Int.toNat (Int.ceil (C₁ * Real.rpow (s : ℝ) (2 : ℝ)))) (A 1) ⊆
          Ball s (DoublyMacroSet 2 ∪ (A 1))) ∧
        ¬ (Ball (1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) (2 : ℝ)))) (A 1) ⊆
            Ball s (DoublyMacroSet 2 ∪ (A 1))) := by
    have := hprop s hsB
    simpa [show ((2 : ℝ) / (2 - 1)) = (2 : ℝ) by norm_num] using this
  exact hspec.2 hscontain

theorem theorem5_not_b2: ¬ (let M := DoublyMacroSet (2 : ℕ);
      (∃ (d1 d2 : ℝ),
          ∀ (x : ℕ), x ≥ (2 : ℕ) ^ (2 : ℕ) →
            0 < d1 ∧
              0 < d2 ∧
                d1 * Real.log (Real.log x) ≤ (M ∩ (Ball x (A 1))).ncard ∧
                  (M ∩ (Ball x (A 1))).ncard ≤ d2 * Real.log (Real.log x)) ∧
        (∃ C₁ C₂ B : ℝ,
          0 < C₁ ∧
            0 < C₂ ∧
              (∀ (s : ℕ), (s : ℝ) ≥ B →
                let rs := Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1))
                (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆
                    Ball s (M ∪ (A 1))) ∧
                  ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs) (A 1) ⊆
                      Ball s (M ∪ (A 1)))))) := by
  intro h
  rcases (by simpa using h) with ⟨_, hexp⟩
  rcases hexp with ⟨C₁, hC₁, C₂, hC₂, B, hB⟩
  refine theorem5_expansion_not_b2 ?_
  refine ⟨C₁, C₂, B, hC₁, hC₂, ?_⟩
  intro s hs
  simpa using hB s hs


theorem theorem5_false: ¬ ((b : ℕ) → (2 ≤ b) →
      let M := DoublyMacroSet b
      (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b ^ b) → 0 < d1 ∧ 0 < d2
          ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ (Ball x (A 1))).ncard
          ∧ (M ∩ (Ball x (A 1))).ncard ≤ d2 * (Real.log (Real.log x))) ∧
      (∃ C₁ C₂ B : ℝ,
        0 < C₁ ∧ 0 < C₂ ∧
        (∀ (s : ℕ), (s ≥ B) →
          let rs := Real.rpow s ((b : ℝ) / (b - 1))
          (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
            ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆
                Ball s (M ∪ (A 1))))) := by
  intro h
  have hb2 : (2 : ℕ) ≤ 2 := by decide
  have h2 := h 2 hb2
  exact theorem5_not_b2 h2


theorem two_le_two_div_mul_of_le (c y : ℝ) (hc : 0 < c) (hcy : c ≤ y) : (2 : ℝ) ≤ (2 / c) * y := by
  have h2 : (2 : ℝ) * c ≤ (2 : ℝ) * y := by
    have h0 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact mul_le_mul_of_nonneg_left hcy h0
  have hgoal : (2 : ℝ) ≤ (2 * y) / c := by
    exact (le_div_iff₀ hc).2 (by simpa [mul_assoc] using h2)
  simpa [div_mul_eq_mul_div] using hgoal

theorem natlog_natlog_doublelog_upper_explicit (b : ℕ) (hb : 2 ≤ b) :
  ∀ (x : ℕ), x ≥ b ^ b →
    (Nat.log b (Nat.log b x) + 1 : ℕ) ≤
      ((1 / Real.log b) + (2 / Real.log (Real.log (b ^ b)))) * Real.log (Real.log x) := by
  intro x hx
  set k : ℕ := Nat.log b (Nat.log b x)
  set y : ℝ := Real.log (Real.log x)
  have hbounds :
      (k : ℝ) * Real.log b + Real.log (Real.log b) ≤ Real.log (Real.log x) ∧
        Real.log (Real.log x) < ((k + 1 : ℕ) : ℝ) * Real.log b + Real.log (Real.log b) := by
    simpa [k] using (natlog_natlog_real_loglog_bounds b x hb hx)
  have h1 : (k : ℝ) * Real.log b + Real.log (Real.log b) ≤ y := by
    simpa [y] using hbounds.1

  -- positivity of log b
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have h1b : (1 : ℕ) < b := lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hb
    exact_mod_cast h1b
  have hlogbpos : 0 < Real.log b := by
    simpa using (Real.log_pos hb1)

  -- from bounds: k*log b ≤ y - loglog b
  have hklogb : (k : ℝ) * Real.log b ≤ y - Real.log (Real.log b) := by
    linarith

  -- (k+1)*log b ≤ y - loglog b + log b
  have hk1logb : ((k + 1 : ℕ) : ℝ) * Real.log b ≤ y - Real.log (Real.log b) + Real.log b := by
    have hklogb_add : (k : ℝ) * Real.log b + Real.log b ≤ y - Real.log (Real.log b) + Real.log b := by
      linarith [hklogb]
    simpa [Nat.cast_add, Nat.cast_one, add_mul, one_mul, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hklogb_add

  -- bound -loglog b by log b
  have hneg : -Real.log (Real.log b) ≤ Real.log b := neg_loglogb_le_logb b hb
  have htmp : y - Real.log (Real.log b) + Real.log b ≤ y + 2 * Real.log b := by
    linarith [hneg]
  have hk1logb2 : ((k + 1 : ℕ) : ℝ) * Real.log b ≤ y + 2 * Real.log b :=
    le_trans hk1logb htmp

  -- divide by log b
  have hk1_le_div : ((k + 1 : ℕ) : ℝ) ≤ (y + 2 * Real.log b) / Real.log b :=
    (le_div_iff₀ hlogbpos).2 hk1logb2
  have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (1 / Real.log b) * y + 2 := by
    have hlogbne : (Real.log b) ≠ 0 := ne_of_gt hlogbpos
    have hrewrite : (y + 2 * Real.log b) / Real.log b = (1 / Real.log b) * y + 2 := by
      calc
        (y + 2 * Real.log b) / Real.log b
            = y / Real.log b + (2 * Real.log b) / Real.log b := by
                simpa [add_div]
        _   = (1 / Real.log b) * y + (2 * Real.log b) / Real.log b := by
                simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        _   = (1 / Real.log b) * y + 2 := by
                simpa [mul_div_cancel_right, hlogbne]
    simpa [hrewrite] using hk1_le_div

  -- absorb the constant 2 into a multiple of y
  have hy_ge : Real.log (Real.log (b ^ b)) ≤ y := by
    simpa [y] using loglog_mono_ge_bpowb b x hb hx
  have hc : 0 < Real.log (Real.log (b ^ b)) := by
    simpa using loglog_pos_of_ge_bpowb b (b ^ b) hb (by exact le_rfl)
  have h2le : (2 : ℝ) ≤ (2 / Real.log (Real.log (b ^ b))) * y :=
    two_le_two_div_mul_of_le (Real.log (Real.log (b ^ b))) y hc hy_ge

  have hk1'' : ((k + 1 : ℕ) : ℝ) ≤ (1 / Real.log b) * y + (2 / Real.log (Real.log (b ^ b))) * y := by
    have hstep : (1 / Real.log b) * y + 2 ≤ (1 / Real.log b) * y + (2 / Real.log (Real.log (b ^ b))) * y := by
      linarith [h2le]
    exact le_trans hk1_le hstep

  have hk1_final : ((k + 1 : ℕ) : ℝ) ≤
      ((1 / Real.log b) + (2 / Real.log (Real.log (b ^ b)))) * y := by
    simpa [add_mul] using hk1''

  -- finish
  simpa [k, y] using hk1_final

theorem natlog_natlog_doublelog_bounds (b : ℕ) (hb : 2 ≤ b) :
  ∃ (c1 c2 : ℝ), 0 < c1 ∧ 0 < c2 ∧
    ∀ (x : ℕ), x ≥ b ^ b →
      c1 * Real.log (Real.log x) ≤ (Nat.log b (Nat.log b x) + 1 : ℕ) ∧
      (Nat.log b (Nat.log b x) + 1 : ℕ) ≤ c2 * Real.log (Real.log x) := by
  classical
  refine ⟨(1 / (2 * Real.log b)), ((1 / Real.log b) + (2 / Real.log (Real.log (b ^ b)))), ?_, ?_, ?_⟩
  ·
    -- c1 > 0
    have hb1nat : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1nat
    have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hb1
    have hden : 0 < (2 : ℝ) * Real.log (b : ℝ) := by
      exact mul_pos (by norm_num) hlogb
    simpa [div_eq_mul_inv] using (div_pos (by norm_num : (0 : ℝ) < 1) hden)
  ·
    -- c2 > 0
    have hb1nat : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1nat
    have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hb1
    have hterm1 : 0 < (1 : ℝ) / Real.log (b : ℝ) := div_pos (by norm_num) hlogb
    have hloglogbb : 0 < Real.log (Real.log (b ^ b)) := by
      simpa using (loglog_pos_of_ge_bpowb b (b ^ b) hb (by exact le_rfl))
    have hterm2 : 0 < (2 : ℝ) / Real.log (Real.log (b ^ b)) := div_pos (by norm_num) hloglogbb
    have :
        0 < (1 : ℝ) / Real.log (b : ℝ) + (2 : ℝ) / Real.log (Real.log (b ^ b)) :=
      add_pos hterm1 hterm2
    simpa using this
  ·
    intro x hx
    constructor
    ·
      -- lower bound
      -- use explicit lemma and rewrite constants
      have h := natlog_natlog_doublelog_lower_explicit b hb x hx
      -- h : (1 / (2 * Real.log b)) * Real.log (Real.log x) ≤ (Nat.log b (Nat.log b x) + 1 : ℕ)
      simpa [mul_assoc] using h
    ·
      -- upper bound
      have h := natlog_natlog_doublelog_upper_explicit b hb x hx
      -- h : (Nat.log b (Nat.log b x) + 1 : ℕ) ≤ ((1 / Real.log b) + (2 / Real.log (Real.log (b ^ b)))) * Real.log (Real.log x)
      simpa [mul_assoc] using h

theorem theorem5_density (b : ℕ) (hb : 2 ≤ b) :
  ∃ (d1 d2 : ℝ), ∀ (x : ℕ), x ≥ b ^ b →
    0 < d1 ∧ 0 < d2 ∧
      d1 * (Real.log (Real.log x)) ≤ ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard ∧
      ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard ≤ d2 * (Real.log (Real.log x)) := by
  classical
  obtain ⟨c1, c2, hc1, hc2, hbounds⟩ := natlog_natlog_doublelog_bounds b hb
  refine ⟨c1, c2, ?_⟩
  intro x hx
  have hcard : ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 :=
    doublyMacro_inter_ball_ncard b x hb hx
  have hbx := hbounds x hx
  refine ⟨hc1, hc2, ?_, ?_⟩
  · simpa [hcard] using hbx.1
  · simpa [hcard] using hbx.2
