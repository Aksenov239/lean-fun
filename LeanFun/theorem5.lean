import LeanFun.Definitions

open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, 0 ≤ j ∧ m = Multiset.replicate (b ^ (b ^ j)) i }

theorem b_le_pow_b (b : ℕ) (hb : 2 ≤ b) : b ≤ b ^ b := by
  have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
  have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hb0 : b ≠ 0 := Nat.ne_of_gt hbpos
  simpa using (le_self_pow hb1 hb0)

theorem ball_A1_mem_iff_card_le (R : ℕ) (m : FreeAbelianMonoid 1) : m ∈ Ball R (A 1) ↔ m.card ≤ R := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hlR, hlA, hsum⟩

    have hcard_sum : (l.sum : Multiset (Fin 1)).card = (l.map Multiset.card).sum := by
      simpa using (Multiset.cardHom.map_list_sum l)

    have hcard_one : ∀ x : Multiset (Fin 1), x ∈ l → x.card = 1 := by
      intro x hx
      have hxA : x ∈ A 1 := hlA x hx
      rcases hxA with ⟨i, rfl⟩
      simpa using (Multiset.card_singleton i)

    have hsum_cards : (l.map Multiset.card).sum = l.length := by
      -- general lemma by induction on l
      have : ∀ l : List (Multiset (Fin 1)), (∀ x ∈ l, x.card = 1) → (l.map Multiset.card).sum = l.length := by
        intro l
        induction l with
        | nil =>
            intro h
            simp
        | cons a t ih =>
            intro h
            have ha : a.card = 1 := h a (by simp)
            have ht : (t.map Multiset.card).sum = t.length := by
              apply ih
              intro x hx
              exact h x (by simp [hx])
            -- reduce to arithmetic
            -- (a :: t).map card sum = a.card + ...
            -- (a :: t).length = t.length.succ
            --
            -- after rewriting ha and ht, goal becomes `1 + t.length = t.length + 1`
            --
            simpa [ha, ht, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      exact this l (by
        intro x hx
        exact hcard_one x hx)

    have hmcard : m.card = l.length := by
      calc
        m.card = (l.sum : Multiset (Fin 1)).card := by simpa [hsum]
        _ = (l.map Multiset.card).sum := hcard_sum
        _ = l.length := hsum_cards

    -- conclude
    rw [hmcard]
    exact hlR

  · intro hmcard
    let i0 : Fin 1 := 0

    have hfun : (fun _ : Fin 1 => i0) = (id : Fin 1 → Fin 1) := by
      funext x
      exact Subsingleton.elim i0 x

    have hmrep : m = Multiset.replicate m.card i0 := by
      have hconst : m.map (fun _ : Fin 1 => i0) = Multiset.replicate m.card i0 := by
        simpa using (Multiset.map_const' m i0)
      have hconst' : m.map id = Multiset.replicate m.card i0 := by
        simpa [hfun] using hconst
      calc
        m = m.map id := by simpa using (Multiset.map_id m).symm
        _ = Multiset.replicate m.card i0 := hconst'

    let l : List (Multiset (Fin 1)) := List.replicate m.card ({i0} : Multiset (Fin 1))

    refine ⟨l, ?_, ?_, ?_⟩
    · -- length bound
      simpa [l] using hmcard
    · -- all entries in A 1
      intro x hx
      have hx' : x = ({i0} : Multiset (Fin 1)) := by
        -- membership in replicate list
        simpa [l] using (List.mem_replicate.mp hx).2
      subst hx'
      exact ⟨i0, rfl⟩
    · -- sum equals m
      have hsum' : l.sum = (m.card • ({i0} : Multiset (Fin 1))) := by
        simpa [l] using (List.sum_replicate m.card ({i0} : Multiset (Fin 1)))
      have hsum'' : l.sum = Multiset.replicate m.card i0 := by
        -- rewrite the nsmul
        --
        -- Multiset.nsmul_singleton : n • ({a} : Multiset α) = replicate n a
        --
        simpa [Multiset.nsmul_singleton] using hsum'
      -- now rewrite using hmrep
      exact hsum''.trans hmrep.symm

def dblMacroVal (b j : ℕ) : ℕ := b ^ (b ^ j)

def dblMacroElem (b j : ℕ) : FreeAbelianMonoid 1 :=
  Multiset.replicate (dblMacroVal b j) (0 : Fin 1)

theorem dblMacroElem_card (b j : ℕ) : (dblMacroElem b j).card = dblMacroVal b j := by
  unfold dblMacroElem dblMacroVal
  simp

theorem dblMacroElem_injective (b : ℕ) (hb : 2 ≤ b) : Function.Injective (dblMacroElem b) := by
  intro j1 j2 h
  have hval : dblMacroVal b j1 = dblMacroVal b j2 := by
    have h' : Multiset.replicate (dblMacroVal b j1) (0 : Fin 1) =
        Multiset.replicate (dblMacroVal b j2) (0 : Fin 1) := by
      simpa [dblMacroElem] using h
    exact (Multiset.replicate_left_injective (0 : Fin 1)) h'
  have hpow : Function.Injective (fun n : ℕ => b ^ n) := Nat.pow_right_injective hb
  have hbpow : b ^ j1 = b ^ j2 := by
    apply hpow
    simpa [dblMacroVal] using hval
  exact hpow hbpow

theorem dblMacroVal_le_iff_le_natLog_natLog (b x j : ℕ) (hb : 2 ≤ b) (hx : x ≥ b) :
  dblMacroVal b j ≤ x ↔ j ≤ Nat.log b (Nat.log b x) := by
  unfold dblMacroVal
  have hb' : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
  have hx0 : x ≠ 0 := by
    have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
    have hxpos : 0 < x := lt_of_lt_of_le hbpos hx
    exact ne_of_gt hxpos
  have hlog0 : Nat.log b x ≠ 0 := by
    have hlogpos : 0 < Nat.log b x := Nat.log_pos hb' hx
    exact ne_of_gt hlogpos
  have h1 : b ^ (b ^ j) ≤ x ↔ b ^ j ≤ Nat.log b x := by
    simpa using (Nat.pow_le_iff_le_log (b := b) hb' (x := b ^ j) (y := x) hx0)
  have h2 : b ^ j ≤ Nat.log b x ↔ j ≤ Nat.log b (Nat.log b x) := by
    simpa using (Nat.pow_le_iff_le_log (b := b) hb' (x := j) (y := Nat.log b x) hlog0)
  exact h1.trans h2

theorem dblMacroVal_mono (b k l : ℕ) (hb : 2 ≤ b) : k ≤ l → dblMacroVal b k ≤ dblMacroVal b l := by
  intro hkl
  have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
  have h1 : b ^ k ≤ b ^ l := pow_le_pow_right' hb1 hkl
  -- now raise both sides to the power b
  have h2 : b ^ (b ^ k) ≤ b ^ (b ^ l) := pow_le_pow_right' hb1 h1
  simpa [dblMacroVal] using h2

theorem dblMacroVal_succ_eq_pow (b k : ℕ) : dblMacroVal b (k + 1) = (dblMacroVal b k) ^ b := by
  unfold dblMacroVal
  rw [pow_succ]
  rw [pow_mul]

theorem doublyMacroSet_mem_iff (b : ℕ) (m : FreeAbelianMonoid 1) : m ∈ DoublyMacroSet b ↔ ∃ j : ℕ, m = dblMacroElem b j := by
  constructor
  · intro hm
    have hm' : ∃ i : Fin 1, ∃ j : ℕ, 0 ≤ j ∧ m = Multiset.replicate (b ^ (b ^ j)) i := by
      simpa [DoublyMacroSet] using hm
    rcases hm' with ⟨i, j, hj, rfl⟩
    refine ⟨j, ?_⟩
    -- show replicate ... i = dblMacroElem b j
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    subst hi
    simp [dblMacroElem, dblMacroVal]
  · rintro ⟨j, rfl⟩
    -- show dblMacroElem b j ∈ DoublyMacroSet b
    have : ∃ i : Fin 1, ∃ j' : ℕ, 0 ≤ j' ∧ dblMacroElem b j = Multiset.replicate (b ^ (b ^ j')) i := by
      refine ⟨(0 : Fin 1), j, ?_, ?_⟩
      · exact Nat.zero_le j
      · simp [dblMacroElem, dblMacroVal]
    -- convert to membership
    simpa [DoublyMacroSet] using this


theorem exists_k_dblMacroVal_pow_gt (b s : ℕ) (hb : 2 ≤ b) : ∃ k : ℕ, s < (dblMacroVal b k) ^ (b - 1) := by
  have hb1 : 1 < b := lt_of_lt_of_le (Nat.lt_succ_self 1) hb
  have hb_ge1 : 1 ≤ b := Nat.le_of_lt hb1

  set L : ℕ := Nat.log b (s + 1) with hL
  have hsL : s < b ^ L.succ := by
    have hs' : s < b ^ (Nat.log b (s + 1)).succ := by
      exact lt_trans (Nat.lt_succ_self s) (Nat.lt_pow_succ_log_self hb1 (s + 1))
    simpa [hL] using hs'

  set k : ℕ := (Nat.log b L.succ).succ with hk

  have hLk : L.succ ≤ b ^ k := by
    have hlt : L.succ < b ^ (Nat.log b L.succ).succ := Nat.lt_pow_succ_log_self hb1 L.succ
    have hle : L.succ ≤ b ^ (Nat.log b L.succ).succ := Nat.le_of_lt hlt
    simpa [hk] using hle

  have hsExp : s < b ^ (b ^ k) := by
    have hpow : b ^ L.succ ≤ b ^ (b ^ k) := pow_le_pow_right' hb_ge1 hLk
    exact lt_of_lt_of_le hsL hpow

  have hbsub_ne : b - 1 ≠ 0 := by
    have hbsub_pos : 0 < b - 1 := tsub_pos_of_lt hb1
    exact Nat.ne_of_gt hbsub_pos

  have hlePow : b ^ (b ^ k) ≤ (b ^ (b ^ k)) ^ (b - 1) := by
    refine le_self_pow ?_ hbsub_ne
    exact one_le_pow₀ hb_ge1

  refine ⟨k, ?_⟩
  have : s < (b ^ (b ^ k)) ^ (b - 1) := lt_of_lt_of_le hsExp hlePow
  simpa [dblMacroVal] using this

theorem fin1_multiset_eq_replicate_card (m : FreeAbelianMonoid 1) : m = Multiset.replicate m.card (0 : Fin 1) := by
  classical
  have hfun : (fun _ : Fin 1 => (0 : Fin 1)) = id := by
    funext x
    exact Subsingleton.elim _ _
  have hmap : m.map id = m.map (fun _ : Fin 1 => (0 : Fin 1)) := by
    exact congrArg (fun f : Fin 1 → Fin 1 => m.map f) hfun.symm
  calc
    m = m.map id := by
      simpa using (Multiset.map_id m).symm
    _ = m.map (fun _ : Fin 1 => (0 : Fin 1)) := by
      exact hmap
    _ = Multiset.replicate m.card (0 : Fin 1) := by
      simpa using (Multiset.map_const' (s := m) (b := (0 : Fin 1)))

theorem list_sum_replicate_eq_replicate_sum (l : List ℕ) : (l.map (fun n => Multiset.replicate n (0 : Fin 1))).sum = Multiset.replicate l.sum (0 : Fin 1) := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      -- expand sums and use additivity of `Multiset.replicate`
      simp [List.sum_cons, ih, Multiset.replicate_add, add_assoc, add_comm, add_left_comm]

theorem ball_macro_union_mem_iff_coinList (b s : ℕ) (m : FreeAbelianMonoid 1) :
  m ∈ Ball s (DoublyMacroSet b ∪ A 1) ↔
    ∃ l : List ℕ,
      l.length ≤ s ∧
        (∀ n ∈ l, n = 1 ∨ ∃ j : ℕ, n = dblMacroVal b j) ∧
        l.sum = m.card := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨L, hLen, hMem, hSum⟩
    let l : List ℕ := L.map Multiset.card
    refine ⟨l, ?_, ?_, ?_⟩
    · simpa [l] using hLen
    · intro n hn
      rcases (List.mem_map.1 hn) with ⟨x, hxL, rfl⟩
      have hxX : x ∈ DoublyMacroSet b ∪ A 1 := hMem x hxL
      rcases hxX with hxD | hxA
      · rcases (doublyMacroSet_mem_iff b x).1 hxD with ⟨j, rfl⟩
        right
        refine ⟨j, ?_⟩
        simpa [dblMacroElem_card]
      · rcases hxA with ⟨i, rfl⟩
        left
        simpa using (Multiset.card_singleton i)
    · have hcard : (L.sum).card = l.sum := by
        simpa [l] using (Multiset.cardHom.map_list_sum L)
      have hSumCard : (L.sum).card = m.card := by
        simpa [hSum] using congrArg Multiset.card hSum
      -- use the two equalities to identify `l.sum`
      calc
        l.sum = (L.sum).card := by simpa [hcard] using hcard.symm
        _ = m.card := hSumCard
  · rintro ⟨l, hLen, hCoins, hSum⟩
    let L : List (FreeAbelianMonoid 1) := l.map (fun n => Multiset.replicate n (0 : Fin 1))
    refine ⟨L, ?_, ?_, ?_⟩
    · simpa [L] using hLen
    · intro x hx
      rcases (List.mem_map.1 hx) with ⟨n, hnL, rfl⟩
      have hcoin : n = 1 ∨ ∃ j : ℕ, n = dblMacroVal b j := hCoins n hnL
      rcases hcoin with rfl | ⟨j, rfl⟩
      · right
        refine ⟨(0 : Fin 1), ?_⟩
        rfl
      · left
        refine (doublyMacroSet_mem_iff b (dblMacroElem b j)).2 ?_
        exact ⟨j, rfl⟩
    · have hLsum : L.sum = Multiset.replicate l.sum (0 : Fin 1) := by
        simpa [L] using (list_sum_replicate_eq_replicate_sum l)
      have hmrep : m = Multiset.replicate m.card (0 : Fin 1) := fin1_multiset_eq_replicate_card m
      calc
        L.sum = Multiset.replicate l.sum (0 : Fin 1) := hLsum
        _ = Multiset.replicate m.card (0 : Fin 1) := by simpa [hSum]
        _ = m := hmrep.symm

theorem logb_logb_div2_eq_affine (b x : ℝ) (hb : 1 < b) (hx : 1 < x) :
  Real.logb b (Real.logb b x / 2) =
    (Real.log (Real.log x) - Real.log (Real.log b) - Real.log 2) / Real.log b := by
  have hb0 : Real.log b ≠ 0 := by
    exact ne_of_gt (Real.log_pos hb)
  have hx0 : Real.log x ≠ 0 := by
    exact ne_of_gt (Real.log_pos hx)
  have hlogbx0 : Real.logb b x ≠ 0 := by
    dsimp [Real.logb]
    exact div_ne_zero hx0 hb0
  have h2 : (2 : ℝ) ≠ 0 := by
    norm_num
  calc
    Real.logb b (Real.logb b x / 2) = Real.log (Real.logb b x / 2) / Real.log b := by
      rfl
    _ = (Real.log (Real.logb b x) - Real.log 2) / Real.log b := by
      rw [Real.log_div hlogbx0 h2]
    _ = ((Real.log (Real.log x) - Real.log (Real.log b)) - Real.log 2) / Real.log b := by
      have hlog : Real.log (Real.logb b x) = Real.log (Real.log x) - Real.log (Real.log b) := by
        simpa [Real.logb] using (Real.log_div hx0 hb0)
      rw [hlog]
    _ = (Real.log (Real.log x) - Real.log (Real.log b) - Real.log 2) / Real.log b := by
      rfl

theorem logb_logb_eq_affine (b x : ℝ) (hb : 1 < b) (hx : 1 < x) :
  Real.logb b (Real.logb b x) =
    (Real.log (Real.log x) - Real.log (Real.log b)) / Real.log b := by
  have hb0 : Real.log b ≠ 0 := by
    exact ne_of_gt (Real.log_pos hb)
  have hx0 : Real.log x ≠ 0 := by
    exact ne_of_gt (Real.log_pos hx)
  -- unfold and use log_div
  simp [Real.logb, Real.log_div hx0 hb0, hb0, hx0]

theorem logb_lt_natLog_add_one (b x : ℕ) : Real.logb b x < (Nat.log b x : ℝ) + 1 := by
  -- Attempt following the suggested strategy
  have h := Nat.lt_floor_add_one (Real.logb b x)
  -- `h` : Real.logb b x < (⌊Real.logb b x⌋₊ : ℝ) + 1
  -- Rewrite the natFloor using the provided lemma.
  simpa [Real.natFloor_logb_natCast] using h


theorem loglog_pos_and_L0_le (b x : ℕ) (hb : 2 ≤ b) (hx : b ^ b ≤ x) :
  (0 : ℝ) < Real.log (Real.log (x : ℝ)) ∧
    Real.log (Real.log ((b ^ b : ℕ) : ℝ)) ≤ Real.log (Real.log (x : ℝ)) := by
  -- establish a crude lower bound `4 ≤ b^b ≤ x`
  have hb1 : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have h4_le_b2 : (4 : ℕ) ≤ b ^ 2 := by
    -- `2^2 ≤ b^2`
    have h2pow : (2 : ℕ) ^ 2 ≤ b ^ 2 := (pow_le_pow_left' hb) 2
    simpa using h2pow
  have hb2_le_bpow : b ^ 2 ≤ b ^ b := by
    -- monotonicity in the exponent since `1 ≤ b` and `2 ≤ b`
    simpa using (pow_le_pow_right' hb1 hb)
  have h4_le_bb : (4 : ℕ) ≤ b ^ b := le_trans h4_le_b2 hb2_le_bpow
  have h4_le_x : (4 : ℕ) ≤ x := le_trans h4_le_bb hx

  have hx4_real : (4 : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast h4_le_x

  -- `Real.exp 1 < x`
  have hexp1_lt_4 : Real.exp (1 : ℝ) < (4 : ℝ) := by
    have hlt : Real.exp (1 : ℝ) < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have hlt4 : (2.7182818286 : ℝ) < (4 : ℝ) := by
      norm_num
    exact lt_trans hlt hlt4
  have hexp1_lt_x : Real.exp (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le hexp1_lt_4 hx4_real

  -- hence `1 < log x`
  have hlogx_gt_one : (1 : ℝ) < Real.log (x : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos (1 : ℝ)) hexp1_lt_x
    -- `log (exp 1) = 1`
    simpa using (by
      simpa using (show Real.log (Real.exp (1 : ℝ)) < Real.log (x : ℝ) from h))

  have hpos_loglogx : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := by
    exact Real.log_pos hlogx_gt_one

  -- Monotonicity: `log (log (b^b)) ≤ log (log x)`
  have hx_pow_real : ((b ^ b : ℕ) : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast hx

  have hbpow_gt_one : (1 : ℝ) < Real.log ((b ^ b : ℕ) : ℝ) := by
    -- show `exp 1 < b^b` using `exp 1 < 4 ≤ b^b`
    have hb4_real : (4 : ℝ) ≤ ((b ^ b : ℕ) : ℝ) := by
      exact_mod_cast h4_le_bb
    have hexp1_lt_bb : Real.exp (1 : ℝ) < ((b ^ b : ℕ) : ℝ) :=
      lt_of_lt_of_le hexp1_lt_4 hb4_real
    have h := Real.log_lt_log (Real.exp_pos (1 : ℝ)) hexp1_lt_bb
    simpa using (by
      simpa using (show Real.log (Real.exp (1 : ℝ)) < Real.log ((b ^ b : ℕ) : ℝ) from h))

  have hlog_bb_le_log_x : Real.log ((b ^ b : ℕ) : ℝ) ≤ Real.log (x : ℝ) := by
    exact Real.log_le_log (by
      -- positivity of `b^b`
      have hb4_real : (4 : ℝ) ≤ ((b ^ b : ℕ) : ℝ) := by
        exact_mod_cast h4_le_bb
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hb4_real
    ) hx_pow_real

  have hloglog_bb_le_loglog_x : Real.log (Real.log ((b ^ b : ℕ) : ℝ)) ≤ Real.log (Real.log (x : ℝ)) := by
    have hlog_bb_pos : (0 : ℝ) < Real.log ((b ^ b : ℕ) : ℝ) :=
      lt_trans (by norm_num : (0 : ℝ) < 1) hbpow_gt_one
    exact Real.log_le_log hlog_bb_pos hlog_bb_le_log_x

  exact ⟨hpos_loglogx, hloglog_bb_le_loglog_x⟩

theorem macro_index_set_ncard_eq_natLog (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b) :
  ({j : ℕ | dblMacroVal b j ≤ x}).ncard = Nat.log b (Nat.log b x) + 1 := by
  classical
  let K : ℕ := Nat.log b (Nat.log b x)
  have hset : ({j : ℕ | dblMacroVal b j ≤ x} : Set ℕ) = Set.Iic K := by
    ext j
    -- unfold membership in both sets and use the given characterization
    simpa [K, Set.Iic] using (dblMacroVal_le_iff_le_natLog_natLog b x j hb hx)
  -- compute the cardinality of `Set.Iic K`
  have hcard : (Set.Iic K : Set ℕ).ncard = K + 1 := by
    calc
      (Set.Iic K : Set ℕ).ncard = (Set.Iic K : Set ℕ).toFinset.card := by
        simpa using (Set.ncard_eq_toFinset_card' (s := (Set.Iic K : Set ℕ)))
      _ = Fintype.card (Set.Iic K) := by
        simpa using (Set.toFinset_card (s := (Set.Iic K : Set ℕ)))
      _ = K + 1 := by
        simpa using (Nat.card_fintypeIic (b := K))
  -- finish
  simpa [hset, hcard, K]


theorem macro_inter_ball_ncard_eq (b x : ℕ) (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  (M ∩ Ball x (A 1)).ncard = ({j : ℕ | dblMacroVal b j ≤ x}).ncard := by
  classical
  -- unfold the `let M := ...`
  simp

  let f : ℕ → FreeAbelianMonoid 1 := dblMacroElem b
  have hf_inj : Function.Injective f := by
    simpa [f] using dblMacroElem_injective b hb

  have hset : (DoublyMacroSet b ∩ Ball x (A 1)) = f '' {j : ℕ | dblMacroVal b j ≤ x} := by
    ext m
    constructor
    · intro hm
      rcases hm with ⟨hmM, hmB⟩
      rcases (doublyMacroSet_mem_iff b m).1 hmM with ⟨j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      have hcard : (dblMacroElem b j).card ≤ x :=
        (ball_A1_mem_iff_card_le x (dblMacroElem b j)).1 hmB
      simpa [dblMacroElem, dblMacroVal] using hcard
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (doublyMacroSet_mem_iff b (f j)).2 ⟨j, rfl⟩
      · exact (ball_A1_mem_iff_card_le x (f j)).2 (by
          simpa [f, dblMacroElem, dblMacroVal] using hj)

  calc
    (DoublyMacroSet b ∩ Ball x (A 1)).ncard
        = (f '' {j : ℕ | dblMacroVal b j ≤ x}).ncard := by
            simpa [hset]
    _ = ({j : ℕ | dblMacroVal b j ≤ x}).ncard := by
          simpa using (Set.ncard_image_of_injective (s := {j : ℕ | dblMacroVal b j ≤ x}) hf_inj)


theorem macro_inter_ball_ncard_eq_natLog (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b) :
  let M := DoublyMacroSet b
  (M ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 := by
  simpa using (macro_inter_ball_ncard_eq b x hb).trans
    (macro_index_set_ncard_eq_natLog b x hb hx)


theorem natLog_ge_logb_sub_one (b x : ℕ) : Real.logb b x - 1 < (Nat.log b x : ℝ) := by
  simpa [Real.natFloor_logb_natCast] using (Nat.sub_one_lt_floor (Real.logb b x))

theorem natLog_le_logb (b x : ℕ) : (Nat.log b x : ℝ) ≤ Real.logb b x := by
  simpa using (Real.natLog_le_logb x b)


theorem realLogb_mono (b x y : ℝ) (hb : 1 < b) (hx : 0 < x) (hxy : x ≤ y) : Real.logb b x ≤ Real.logb b y := by
  exact Real.logb_le_logb_of_le (b := b) (x := x) (y := y) hb hx hxy


def theorem5_T (b : ℕ) : ℕ → ℕ
  | 0 => b - 1
  | k + 1 => (dblMacroVal b k) ^ (b - 1) + theorem5_T b k

theorem theorem5_T_le_two_last (b : ℕ) (hb : 2 ≤ b) :
  ∀ k : ℕ, 1 ≤ k →
    theorem5_T b k ≤ 2 * (dblMacroVal b (k - 1)) ^ (b - 1) := by
  intro k hk

  have h_last : ∀ k : ℕ, theorem5_T b k ≤ (dblMacroVal b k) ^ (b - 1) := by
    intro k
    induction k with
    | zero =>
        have hb1 : 1 ≤ b := by omega
        have hbsub_ne0 : b - 1 ≠ 0 := by omega
        have hpow : b ≤ b ^ (b - 1) := le_self_pow hb1 hbsub_ne0
        have hsub : b - 1 ≤ b := Nat.sub_le _ _
        have : b - 1 ≤ b ^ (b - 1) := le_trans hsub hpow
        simpa [theorem5_T, dblMacroVal] using this
    | succ k ih =>
        have hadd :
            (dblMacroVal b k) ^ (b - 1) + theorem5_T b k ≤
              (dblMacroVal b k) ^ (b - 1) + (dblMacroVal b k) ^ (b - 1) :=
          Nat.add_le_add_left ih ((dblMacroVal b k) ^ (b - 1))

        have hsum :
            theorem5_T b (k + 1) ≤ 2 * ((dblMacroVal b k) ^ (b - 1)) := by
          simpa [theorem5_T, two_mul] using hadd

        have ha_ge2 : 2 ≤ (dblMacroVal b k) ^ (b - 1) := by
          have hb1 : 1 ≤ b := by omega
          have hbpos : 0 < b := by omega
          have hkpos : 0 < b ^ k := Nat.pow_pos hbpos
          have hkne0 : b ^ k ≠ 0 := Nat.ne_of_gt hkpos
          have hbase_le : b ≤ b ^ (b ^ k) := le_self_pow hb1 hkne0
          have hbase_ge2 : 2 ≤ b ^ (b ^ k) := le_trans hb hbase_le
          have hbase_ge2' : 2 ≤ dblMacroVal b k := by
            simpa [dblMacroVal] using hbase_ge2
          have hbsub_ne0 : b - 1 ≠ 0 := by omega
          have hbase1 : 1 ≤ dblMacroVal b k := le_trans (by decide : 1 ≤ 2) hbase_ge2'
          have hpow_le : dblMacroVal b k ≤ (dblMacroVal b k) ^ (b - 1) :=
            le_self_pow hbase1 hbsub_ne0
          exact le_trans hbase_ge2' hpow_le

        have ha_ne1 : (dblMacroVal b k) ^ (b - 1) ≠ 1 := by
          have h1lt : 1 < (dblMacroVal b k) ^ (b - 1) :=
            lt_of_lt_of_le Nat.one_lt_two ha_ge2
          exact ne_of_gt h1lt

        have h2pow :
            2 * ((dblMacroVal b k) ^ (b - 1)) ≤ ((dblMacroVal b k) ^ (b - 1)) ^ b := by
          have h2mul :
              ((dblMacroVal b k) ^ (b - 1)) * 2 ≤ ((dblMacroVal b k) ^ (b - 1)) * b :=
            Nat.mul_le_mul_left ((dblMacroVal b k) ^ (b - 1)) hb
          have hmul_pow :
              ((dblMacroVal b k) ^ (b - 1)) * b ≤ ((dblMacroVal b k) ^ (b - 1)) ^ b :=
            Nat.mul_le_pow ha_ne1 b
          have h' :
              ((dblMacroVal b k) ^ (b - 1)) * 2 ≤ ((dblMacroVal b k) ^ (b - 1)) ^ b :=
            le_trans h2mul hmul_pow
          simpa [Nat.mul_comm] using h'

        have hdbl : dblMacroVal b (k + 1) = (dblMacroVal b k) ^ b := by
          simp [dblMacroVal, Nat.pow_succ, pow_mul, Nat.mul_assoc]

        have hpow_eq : ((dblMacroVal b k) ^ (b - 1)) ^ b = (dblMacroVal b (k + 1)) ^ (b - 1) := by
          calc
            ((dblMacroVal b k) ^ (b - 1)) ^ b = (dblMacroVal b k) ^ ((b - 1) * b) := by
              simpa using (pow_mul (dblMacroVal b k) (b - 1) b).symm
            _ = (dblMacroVal b k) ^ (b * (b - 1)) := by
              simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            _ = ((dblMacroVal b k) ^ b) ^ (b - 1) := by
              simpa using (pow_mul (dblMacroVal b k) b (b - 1))
            _ = (dblMacroVal b (k + 1)) ^ (b - 1) := by
              simpa [hdbl]

        have h2a : 2 * ((dblMacroVal b k) ^ (b - 1)) ≤ (dblMacroVal b (k + 1)) ^ (b - 1) := by
          simpa [hpow_eq] using h2pow

        exact le_trans hsum h2a

  cases k with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hk)
  | succ k =>
      have hadd :
          (dblMacroVal b k) ^ (b - 1) + theorem5_T b k ≤
            (dblMacroVal b k) ^ (b - 1) + (dblMacroVal b k) ^ (b - 1) :=
        Nat.add_le_add_left (h_last k) ((dblMacroVal b k) ^ (b - 1))
      simpa [Nat.succ_sub_one, theorem5_T, two_mul] using hadd

theorem theorem5_T_lt_succ (b : ℕ) (hb : 2 ≤ b) : ∀ k : ℕ, theorem5_T b k < theorem5_T b (k + 1) := by
  intro k
  have hbpos : 0 < b := lt_of_lt_of_le (Nat.succ_pos 1) hb
  have hbase : 0 < dblMacroVal b k := by
    dsimp [dblMacroVal]
    exact Nat.pow_pos hbpos
  have hpos : 0 < (dblMacroVal b k) ^ (b - 1) := Nat.pow_pos hbase
  simp [theorem5_T]
  exact Nat.lt_add_of_pos_left hpos


theorem theorem5_T_pos (b : ℕ) (hb : 2 ≤ b) : ∀ k : ℕ, 1 ≤ theorem5_T b k := by
  intro k
  induction k with
  | zero =>
      have h : 1 ≤ b - 1 := by
        simpa using (Nat.sub_le_sub_right hb 1)
      simpa [theorem5_T] using h
  | succ k ih =>
      have hle : theorem5_T b k ≤ (dblMacroVal b k) ^ (b - 1) + theorem5_T b k := by
        exact Nat.le_add_left _ _
      have h : 1 ≤ (dblMacroVal b k) ^ (b - 1) + theorem5_T b k :=
        le_trans ih hle
      simpa [theorem5_T] using h

theorem theorem5_bsub1_le_two_pow_real (b : ℕ) : ((b - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (b - 1) := by
  -- attempt proof using nat inequality and casting
  have hnat : (b - 1) ≤ (2 : ℕ) ^ (b - 1) := by
    have h1 : b - 1 ≤ 2 * (b - 1) := by
      have h1' : b - 1 ≤ (b - 1) + (b - 1) := by
        simpa using (self_le_add_right (b - 1) (b - 1))
      simpa [two_mul] using h1'
    have h2 : 2 * (b - 1) ≤ (2 : ℕ) ^ (b - 1) := by
      simpa using (Nat.mul_le_pow (a := 2) (by decide : (2 : ℕ) ≠ 1) (b - 1))
    exact le_trans h1 h2
  -- cast to real
  exact_mod_cast hnat

theorem theorem5_cast_sub_one (b : ℕ) (hb : 1 ≤ b) : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
  simpa using (Nat.cast_sub (R := ℝ) hb)

def theorem5_coinPred (b : ℕ) (t : ℕ) : Prop :=
  t = 1 ∨ ∃ j : ℕ, t = dblMacroVal b j

def theorem5_Rep (b s n : ℕ) : Prop :=
  ∃ l : List ℕ,
    l.length ≤ s ∧ (∀ t ∈ l, theorem5_coinPred b t) ∧ l.sum = n

theorem theorem5_Rep_lt_dblMacroVal (b : ℕ) (hb : 2 ≤ b) :
  ∀ k n : ℕ, n < dblMacroVal b k → theorem5_Rep b (theorem5_T b k) n := by
  intro k n hn
  induction k generalizing n with
  | zero =>
      refine ⟨List.replicate n 1, ?_, ?_, ?_⟩
      ·
        have hn' : n < b := by
          simpa [dblMacroVal] using hn
        simpa [theorem5_T] using (Order.le_sub_one_of_lt hn')
      ·
        intro t ht
        have ht' : t = 1 := by
          rcases (List.mem_replicate.mp ht) with ⟨_, rfl⟩
          rfl
        left
        exact ht'
      ·
        simp [List.sum_replicate]
  | succ k ih =>
      let mk : ℕ := dblMacroVal b k
      have hb0 : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
      have hmk_pos : 0 < mk := by
        simpa [mk, dblMacroVal] using (pow_pos hb0 (b ^ k))
      have hn' : n < mk ^ b := by
        simpa [mk, dblMacroVal, pow_succ, pow_mul] using hn
      let q : ℕ := n / mk
      let r : ℕ := n % mk
      have hr_lt : r < mk := by
        simpa [r] using Nat.mod_lt n hmk_pos
      have hrRep : theorem5_Rep b (theorem5_T b k) r := by
        apply ih r
        simpa [mk] using hr_lt
      rcases hrRep with ⟨lr, hlr_len, hlr_coin, hlr_sum⟩
      let lq : List ℕ := List.replicate q mk
      refine ⟨lq ++ lr, ?_, ?_, ?_⟩
      · -- length bound
        have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
        have hn_le_mul : n ≤ mk * mk ^ (b - 1) := by
          have hb_eq : b = (b - 1) + 1 := (Nat.sub_add_cancel hb1).symm
          have hn1 : n < mk ^ ((b - 1) + 1) := by
            have hn1 := hn'
            rw [hb_eq] at hn1
            exact hn1
          have hn2 : n < mk ^ (b - 1) * mk := by
            simpa [pow_succ] using hn1
          have hn3 : n < mk * mk ^ (b - 1) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn2
          exact le_of_lt hn3
        have hq_le : q ≤ mk ^ (b - 1) := by
          have h :=
              Nat.div_le_of_le_mul' (m := n) (k := mk) (n := mk ^ (b - 1)) hn_le_mul
          simpa [q] using h
        simpa [theorem5_T, mk, lq, List.length_append] using (Nat.add_le_add hq_le hlr_len)
      · -- coin predicate
        intro t ht
        rcases List.mem_append.mp ht with htq | htr
        · have ht' : t = mk := by
            rcases (List.mem_replicate.mp (by simpa [lq] using htq)) with ⟨_, rfl⟩
            rfl
          subst ht'
          right
          refine ⟨k, ?_⟩
          simp [mk]
        · exact hlr_coin t htr
      · -- sum
        have hlq_sum : lq.sum = q * mk := by
          simp [lq, List.sum_const_nat]
        calc
          (lq ++ lr).sum = lq.sum + lr.sum := by
            simp [List.sum_append]
          _ = q * mk + r := by
            simp [hlq_sum, hlr_sum]
          _ = n := by
            have h := Nat.div_add_mod n mk
            -- h : mk * (n / mk) + n % mk = n
            rw [Nat.mul_comm mk (n / mk)] at h
            simpa [q, r] using h


theorem theorem5_Rep_lt_scaledMacro (b : ℕ) (hb : 2 ≤ b) :
  ∀ k s n : ℕ,
    theorem5_T b k ≤ s →
      n < (s - theorem5_T b k + 1) * dblMacroVal b k →
        theorem5_Rep b s n := by
  intro k s n hTs hn
  set Tk : ℕ := theorem5_T b k
  set m : ℕ := dblMacroVal b k
  have hTk_le_s : Tk ≤ s := by
    simpa [Tk] using hTs
  have hn' : n < (s - Tk + 1) * m := by
    simpa [Tk, m] using hn
  have hbpos : 0 < b := by
    exact lt_of_lt_of_le (Nat.succ_pos 1) hb
  have hmpos : 0 < m := by
    -- m = b^(b^k)
    simpa [m, dblMacroVal] using (Nat.pow_pos (n := b ^ k) hbpos)
  set q : ℕ := n / m
  set r : ℕ := n % m
  have hr_lt : r < m := by
    have : n % m < m := Nat.mod_lt n hmpos
    simpa [r] using this
  have hq_le : q ≤ s - Tk := by
    have hq_lt : q < s - Tk + 1 := by
      have : n / m < s - Tk + 1 := (Nat.div_lt_iff_lt_mul hmpos).2 hn'
      simpa [q] using this
    exact Nat.le_of_lt_succ hq_lt
  have hr_rep : theorem5_Rep b Tk r := by
    have hr_lt' : r < dblMacroVal b k := by
      simpa [m] using hr_lt
    have := theorem5_Rep_lt_dblMacroVal b hb k r hr_lt'
    simpa [Tk] using this
  rcases hr_rep with ⟨l2, hl2_len, hl2_pred, hl2_sum⟩
  refine ⟨(List.replicate q m) ++ l2, ?_, ?_, ?_⟩
  · -- length bound
    calc
      ((List.replicate q m) ++ l2).length = (List.replicate q m).length + l2.length := by
        simp
      _ = q + l2.length := by
        simp
      _ ≤ q + Tk := by
        exact Nat.add_le_add_left hl2_len q
      _ ≤ (s - Tk) + Tk := by
        exact Nat.add_le_add_right hq_le Tk
      _ = s := by
        exact Nat.sub_add_cancel hTk_le_s
  · -- coin predicate
    intro t ht
    have ht' := List.mem_append.1 ht
    cases ht' with
    | inl ht1 =>
        have htEq : t = m := by
          exact List.eq_of_mem_replicate ht1
        subst htEq
        right
        refine ⟨k, ?_⟩
        simp [m]
    | inr ht2 =>
        exact hl2_pred t ht2
  · -- sum
    have hdiv : q * m + r = n := by
      -- Nat.div_add_mod gives m * (n / m) + n % m = n
      simpa [q, r, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.div_add_mod n m)
    calc
      ((List.replicate q m) ++ l2).sum = (List.replicate q m).sum + l2.sum := by
        simp
      _ = q * m + r := by
        simp [hl2_sum]
      _ = n := by
        exact hdiv

theorem theorem5_Rep_le_scaledMacro (b : ℕ) (hb : 2 ≤ b) :
  ∀ k s n : ℕ,
    theorem5_T b k ≤ s →
      n ≤ (s - theorem5_T b k + 1) * dblMacroVal b k →
        theorem5_Rep b s n := by
  intro k s n hTk hn
  rcases lt_or_eq_of_le hn with hnlt | hneq
  ·
    exact theorem5_Rep_lt_scaledMacro b hb k s n hTk hnlt
  ·
    -- equality case
    refine ⟨List.replicate (s - theorem5_T b k + 1) (dblMacroVal b k), ?_⟩
    refine And.intro ?_ ?_
    ·
      -- length bound
      have hpos : 1 ≤ theorem5_T b k := theorem5_T_pos b hb k
      have hlen0 : s - theorem5_T b k + 1 ≤ s := by
        have h := Nat.add_le_add_left hpos (s - theorem5_T b k)
        simpa [Nat.sub_add_cancel hTk] using h
      simpa [List.length_replicate] using hlen0
    ·
      refine And.intro ?_ ?_
      ·
        intro t ht
        have ht' : t = dblMacroVal b k := by
          have : t ∈ [dblMacroVal b k] := (List.replicate_subset_singleton (s - theorem5_T b k + 1) (dblMacroVal b k)) ht
          simpa using this
        subst ht'
        right
        exact ⟨k, rfl⟩
      ·
        -- sum
        -- rewrite n using hneq
        -- goal: (replicate ...).sum = n
        rw [hneq]
        simpa using (List.sum_const_nat (s - theorem5_T b k + 1) (dblMacroVal b k))

theorem theorem5_exists_T_interval (b : ℕ) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ b - 1 →
    ∃ k : ℕ, theorem5_T b k ≤ s ∧ s < theorem5_T b (k + 1) := by
  classical
  intro s hs
  let Q : ℕ → Prop := fun k => s < theorem5_T b (k + 1)
  have hQ : ∃ k : ℕ, Q k := by
    rcases exists_k_dblMacroVal_pow_gt b s hb with ⟨k1, hk1⟩
    refine ⟨k1, ?_⟩
    have : s < (dblMacroVal b k1) ^ (b - 1) + theorem5_T b k1 :=
      lt_of_lt_of_le hk1 (Nat.le_add_right _ _)
    simpa [Q, theorem5_T] using this
  refine ⟨Nat.find hQ, ?_, ?_⟩
  · cases hK : Nat.find hQ with
    | zero =>
        simpa [hK, theorem5_T] using hs
    | succ k' =>
        have hklt : k' < Nat.find hQ := by
          simpa [hK] using Nat.lt_succ_self k'
        have hnot : ¬ Q k' := Nat.find_min hQ hklt
        have hle : theorem5_T b (k' + 1) ≤ s := by
          exact le_of_not_gt hnot
        have hle' : theorem5_T b (Nat.succ k') ≤ s := by
          simpa [Nat.succ_eq_add_one] using hle
        simpa [hK] using hle'
  · simpa [Q] using Nat.find_spec hQ

theorem theorem5_exp_le_two (b : ℕ) (hb : 2 ≤ b) : (b : ℝ) / (b - 1) ≤ 2 := by
  have hb1lt : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1:ℕ) < 2) hb
  have hpos_nat : 0 < b - 1 := Nat.sub_pos_of_lt hb1lt
  have hpos : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpos_nat
  have hb1le : (1 : ℕ) ≤ b := le_trans (by decide : (1:ℕ) ≤ 2) hb
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hb
  -- cast subtraction
  have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    -- `Nat.cast_sub` gives `↑(b-1) = ↑b - ↑1`
    simpa using (Nat.cast_sub hb1le : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - ((1 : ℕ) : ℝ))
  -- clear division
  have hmul : (b : ℝ) ≤ 2 * ((b - 1 : ℕ) : ℝ) := by
    nlinarith [hbR, hcast]
  -- use `div_le_iff₀` (since denominator is positive)
  have h := (div_le_iff₀ hpos).2 (by simpa [mul_assoc] using hmul)
  -- goal has denominator `↑(b-1)`, so rewrite it using `hcast`
  -- and conclude
  simpa [hcast] using h


theorem theorem5_inv_mul_b_eq_div (b : ℕ) :
    (((b - 1 : ℕ) : ℝ)⁻¹) * (b : ℝ) = (b : ℝ) / (b - 1) := by
  by_cases hb : b = 0
  · subst hb
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  · have hb1 : (1 : ℕ) ≤ b := Nat.one_le_iff_ne_zero.mpr hb
    have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) hb1)
    simp [div_eq_mul_inv, hcast, mul_comm, mul_left_comm, mul_assoc]

theorem theorem5_inv_natCast_sub_one (b : ℕ) (hb : 2 ≤ b) : (((b - 1 : ℕ) : ℝ)⁻¹) = ((b : ℝ) - 1)⁻¹ := by
  have hb1 : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (m := 1) (n := b) hb1)
  simp [hcast]

theorem theorem5_part1_density_lower (b : ℕ) (hb : 2 ≤ b) :
  ∃ d1 : ℝ,
    0 < d1 ∧
      ∀ x : ℕ, x ≥ b ^ b →
        d1 * Real.log (Real.log x) ≤ (DoublyMacroSet b ∩ Ball x (A 1)).ncard := by
  classical
  let d1 : ℝ := 1 / (4 * Real.log (b : ℝ))
  refine ⟨d1, ?_, ?_⟩
  · -- show 0 < d1
    have hb1 : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1R : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast hb1
    have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hb1R
    have hden : 0 < (4 : ℝ) * Real.log (b : ℝ) := by nlinarith
    -- d1 = 1 / (4 * log b)
    have : 0 < (1 : ℝ) / ((4 : ℝ) * Real.log (b : ℝ)) := by
      exact div_pos (by positivity) hden
    simpa [d1, div_eq_mul_inv] using this
  · intro x hx
    have hx_b : x ≥ b := by
      -- b ≤ b^b ≤ x
      exact le_trans (b_le_pow_b b hb) hx
    have hncard : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 := by
      simpa using (macro_inter_ball_ncard_eq_natLog b x hb hx_b)
    -- rewrite ncard
    have hypos_and := loglog_pos_and_L0_le b x hb hx
    have hypos : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := hypos_and.1
    set y : ℝ := Real.log (Real.log (x : ℝ))
    have hypos' : 0 < y := by simpa [y] using hypos
    set C : ℝ := Real.log (Real.log (b : ℝ)) + Real.log 2
    have hb1 : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1R : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
    have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1R
    -- derive inequality Real.logb b (Real.logb b x /2) ≤ ncard
    have hlogb_le_ncard :
        Real.logb (b : ℝ) (Real.logb (b : ℝ) (x : ℝ) / 2) ≤
          (Nat.log b (Nat.log b x) + 1 : ℝ) := by
      have hinner_lt : Real.logb (b : ℕ) x - 1 < (Nat.log b x : ℝ) := natLog_ge_logb_sub_one b x
      have hb_logbx_ge2 : (2 : ℝ) ≤ Real.logb (b : ℝ) (x : ℝ) := by
        have hx_cast : ((b ^ b : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
        have hpos : (0 : ℝ) < ((b ^ b : ℕ) : ℝ) := by
          have hbpos : (0 : ℕ) < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
          have : (0 : ℕ) < b ^ b := pow_pos hbpos b
          exact_mod_cast this
        have hmono := realLogb_mono (b := (b : ℝ)) (x := ((b ^ b : ℕ) : ℝ)) (y := (x : ℝ)) hb1R hpos hx_cast
        have hlogb_pow : Real.logb (b : ℝ) ((b : ℝ) ^ b) = (b : ℝ) := by
          simpa [Real.logb_pow, Real.logb_self_eq_one hb1R]
        have hcastpow : ((b ^ b : ℕ) : ℝ) = (b : ℝ) ^ b := by
          norm_cast
        have : (b : ℝ) ≤ Real.logb (b : ℝ) (x : ℝ) := by
          simpa [hcastpow, hlogb_pow] using hmono
        have hb2R : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        exact le_trans hb2R this
      have hhalf_le : Real.logb (b : ℝ) (x : ℝ) / 2 ≤ (Nat.log b x : ℝ) := by
        have hsub_le : Real.logb (b : ℝ) (x : ℝ) / 2 ≤ Real.logb (b : ℝ) (x : ℝ) - 1 := by
          nlinarith [hb_logbx_ge2]
        have hlt : Real.logb (b : ℝ) (x : ℝ) - 1 < (Nat.log b x : ℝ) := by
          simpa using hinner_lt
        exact le_of_lt (lt_of_le_of_lt hsub_le hlt)
      have hxpos : 0 < Real.logb (b : ℝ) (x : ℝ) / 2 := by
        have : 0 < Real.logb (b : ℝ) (x : ℝ) := lt_of_lt_of_le (by norm_num) hb_logbx_ge2
        nlinarith
      have hmono_inner := realLogb_mono (b := (b : ℝ)) (x := Real.logb (b : ℝ) (x : ℝ) / 2)
        (y := (Nat.log b x : ℝ)) hb1R hxpos hhalf_le
      have houter_lt : Real.logb (b : ℕ) (Nat.log b x) - 1 < (Nat.log b (Nat.log b x) : ℝ) :=
        natLog_ge_logb_sub_one b (Nat.log b x)
      have houter_le : Real.logb (b : ℝ) (Nat.log b x : ℝ) < (Nat.log b (Nat.log b x) : ℝ) + 1 := by
        have : Real.logb (b : ℝ) (Nat.log b x : ℝ) - 1 < (Nat.log b (Nat.log b x) : ℝ) := by
          simpa using houter_lt
        linarith
      have houter_le' : Real.logb (b : ℝ) (Nat.log b x : ℝ) ≤ (Nat.log b (Nat.log b x) : ℝ) + 1 :=
        le_of_lt houter_le
      exact le_trans hmono_inner houter_le'
    -- show x > 1 for affine lemma
    have hx1 : (1 : ℕ) < x := by
      have hb_ne0 : b ≠ 0 := by omega
      have hbpow : (1 : ℕ) < b ^ b := by
        exact one_lt_pow' hb1 hb_ne0
      exact lt_of_lt_of_le hbpow hx
    have hx1R : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
    -- case split
    by_cases hsmall : y ≤ 2 * C
    · have hncard_ge1 : (1 : ℝ) ≤ (Nat.log b (Nat.log b x) + 1 : ℝ) := by
        have : (1 : ℕ) ≤ Nat.log b (Nat.log b x) + 1 := by
          exact Nat.succ_le_succ (Nat.zero_le _)
        exact_mod_cast this
      have hC1 : Real.log (Real.log (b : ℝ)) ≤ Real.log (b : ℝ) := by
        have : (0 : ℝ) ≤ Real.log (b : ℝ) := le_of_lt hlogb_pos
        simpa using (Real.log_le_self this)
      have hC2 : Real.log 2 ≤ Real.log (b : ℝ) := by
        have hpos2 : (0 : ℝ) < 2 := by norm_num
        have h2le : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        exact Real.log_le_log hpos2 h2le
      have hC_le : C ≤ 2 * Real.log (b : ℝ) := by
        have : Real.log (Real.log (b : ℝ)) + Real.log 2 ≤ Real.log (b : ℝ) + Real.log (b : ℝ) := by
          linarith [hC1, hC2]
        simpa [C, two_mul, add_comm, add_left_comm, add_assoc] using this
      have hy1 : d1 * y ≤ d1 * (2 * C) := by
        have hd1nonneg : 0 ≤ d1 := le_of_lt (by
          have hb1R : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
          have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hb1R
          have hden : 0 < (4 : ℝ) * Real.log (b : ℝ) := by nlinarith
          have : 0 < (1 : ℝ) / ((4 : ℝ) * Real.log (b : ℝ)) := div_pos (by positivity) hden
          simpa [d1] using this)
        exact mul_le_mul_of_nonneg_left hsmall hd1nonneg
      have hdenpos : 0 < (2 : ℝ) * Real.log (b : ℝ) := by nlinarith [hlogb_pos]
      have hdiv : d1 * (2 * C) ≤ 1 := by
        have hcalc : d1 * (2 * C) = C / ((2 : ℝ) * Real.log (b : ℝ)) := by
          simp [d1, C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          ring
        have hC_le' : C ≤ (2 : ℝ) * Real.log (b : ℝ) := by simpa using hC_le
        have : C / ((2 : ℝ) * Real.log (b : ℝ)) ≤ 1 := (div_le_one hdenpos).2 hC_le'
        simpa [hcalc] using this
      have hy_le : d1 * y ≤ 1 := le_trans hy1 hdiv
      have : d1 * y ≤ (Nat.log b (Nat.log b x) + 1 : ℝ) := le_trans hy_le hncard_ge1
      simpa [y, hncard] using this
    · have hlarge : 2 * C < y := lt_of_not_ge hsmall
      have hC_le_y : y / 2 ≤ y - C := by
        have : (2 : ℝ) * C ≤ y := by linarith
        linarith
      have hlogb_aff :
          Real.logb (b : ℝ) (Real.logb (b : ℝ) (x : ℝ) / 2) = (y - C) / Real.log (b : ℝ) := by
        have : Real.logb (b : ℝ) (Real.logb (b : ℝ) (x : ℝ) / 2) =
            (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ)) - Real.log 2) / Real.log (b : ℝ) :=
          logb_logb_div2_eq_affine (b := (b : ℝ)) (x := (x : ℝ)) hb1R hx1R
        simpa [y, C, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hmain : d1 * y ≤ (y - C) / Real.log (b : ℝ) := by
        have h2 : y / 4 ≤ y - C := by
          have : y / 2 ≤ y - C := hC_le_y
          nlinarith
        have hlogb_pos' : 0 < Real.log (b : ℝ) := hlogb_pos
        have hineq : (y / 4) / Real.log (b : ℝ) ≤ (y - C) / Real.log (b : ℝ) :=
          div_le_div_of_nonneg_right h2 (le_of_lt hlogb_pos')
        have hcalc : d1 * y = (y / 4) / Real.log (b : ℝ) := by
          simp [d1, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        simpa [hcalc] using hineq
      have : d1 * y ≤ Real.logb (b : ℝ) (Real.logb (b : ℝ) (x : ℝ) / 2) := by
        simpa [hlogb_aff] using hmain
      have : d1 * y ≤ (Nat.log b (Nat.log b x) + 1 : ℝ) := le_trans this hlogb_le_ncard
      simpa [y, hncard] using this

theorem theorem5_part1_density_upper (b : ℕ) (hb : 2 ≤ b) :
  ∃ d2 : ℝ,
    0 < d2 ∧
      ∀ x : ℕ, x ≥ b ^ b →
        (DoublyMacroSet b ∩ Ball x (A 1)).ncard ≤ d2 * Real.log (Real.log x) := by
  classical
  let L0 : ℝ := Real.log (Real.log ((b ^ b : ℕ) : ℝ))
  have hL0pos : (0 : ℝ) < L0 := by
    have h := loglog_pos_and_L0_le b (b ^ b) hb (by rfl)
    simpa [L0] using h.1
  have hb1nat : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb1nat
  have hlogbpos : (0 : ℝ) < Real.log (b : ℝ) := Real.log_pos hb1
  let C : ℝ := |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) + 2
  let d2 : ℝ := (1 / Real.log (b : ℝ)) + C / L0
  refine ⟨d2, ?_, ?_⟩
  · -- positivity of d2
    have hCnonneg : (0 : ℝ) ≤ C := by
      have hlogbnonneg : (0 : ℝ) ≤ Real.log (b : ℝ) := le_of_lt hlogbpos
      have : (0 : ℝ) ≤ |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) + 2 := by
        have hdiv_nonneg : (0 : ℝ) ≤ |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) :=
          div_nonneg (abs_nonneg _) hlogbnonneg
        linarith
      simpa [C] using this
    have hCdiv_nonneg : (0 : ℝ) ≤ C / L0 := by
      have hL0nonneg : (0 : ℝ) ≤ L0 := le_of_lt hL0pos
      exact div_nonneg hCnonneg hL0nonneg
    have h1divpos : (0 : ℝ) < (1 / Real.log (b : ℝ)) := by
      exact one_div_pos.mpr hlogbpos
    have : (0 : ℝ) < (1 / Real.log (b : ℝ)) + C / L0 := by
      nlinarith
    simpa [d2] using this
  · intro x hx
    have hxbb : b ^ b ≤ x := hx
    have hbx : b ≤ x := le_trans (b_le_pow_b b hb) hxbb
    have hcard : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 := by
      simpa using (macro_inter_ball_ncard_eq_natLog b x hb hbx)
    have hcardR : ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ) = (Nat.log b (Nat.log b x) + 1 : ℝ) := by
      exact_mod_cast hcard
    have hNatlogpos : 0 < Nat.log b x := Nat.log_pos hb1nat hbx
    have hNatlogposR : (0 : ℝ) < (Nat.log b x : ℝ) := by
      exact_mod_cast hNatlogpos
    have houter : (Nat.log b (Nat.log b x) : ℝ) ≤ Real.logb b (Nat.log b x) := natLog_le_logb b (Nat.log b x)
    have hinner : (Nat.log b x : ℝ) ≤ Real.logb b x := natLog_le_logb b x
    have hlogbmono : Real.logb (b : ℝ) (Nat.log b x) ≤ Real.logb (b : ℝ) (Real.logb b x) := by
      simpa using
        (realLogb_mono (b := (b : ℝ)) (x := (Nat.log b x : ℝ)) (y := Real.logb (b : ℝ) (x : ℝ)) hb1 hNatlogposR
          hinner)
    have hstep : (Nat.log b (Nat.log b x) : ℝ) ≤ Real.logb b (Real.logb b x) :=
      le_trans houter hlogbmono
    have hncard_le : ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ) ≤ Real.logb b (Real.logb b x) + 1 := by
      calc
        ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ)
            = (Nat.log b (Nat.log b x) + 1 : ℝ) := hcardR
        _ = (Nat.log b (Nat.log b x) : ℝ) + 1 := by
              norm_cast
        _ ≤ Real.logb b (Real.logb b x) + 1 := by
              linarith
    -- rewrite logb(logb x) as an affine function of loglog x
    have hx1nat : 1 < x := lt_of_lt_of_le hb1nat hbx
    have hx1 : (1 : ℝ) < (x : ℝ) := by
      exact_mod_cast hx1nat
    have hlogb_aff : Real.logb (b : ℝ) (Real.logb (b : ℝ) (x : ℝ)) =
        (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ))) / Real.log (b : ℝ) := by
      simpa using (logb_logb_eq_affine (b := (b : ℝ)) (x := (x : ℝ)) hb1 hx1)
    have hlogb_aff' : Real.logb b (Real.logb b x) =
        (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ))) / Real.log (b : ℝ) := by
      simpa using hlogb_aff
    -- bounds for loglog x
    have hloglog := loglog_pos_and_L0_le b x hb hxbb
    have hloglogpos : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := hloglog.1
    have hL0le : L0 ≤ Real.log (Real.log (x : ℝ)) := by
      simpa [L0] using hloglog.2
    -- Step 1: bound by (1/log b) * loglog x + C
    have hbound1 : ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ)
        ≤ (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + C := by
      -- it suffices to bound `Real.logb b (Real.logb b x) + 1`
      have hlogb_le : Real.logb b (Real.logb b x) + 1
          ≤ (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + C := by
        -- rewrite the double logb
        rw [hlogb_aff']
        -- expand C and rearrange
        -- Use `-a ≤ |a|` to control the constant term
        have hneg_le_abs : -(Real.log (Real.log (b : ℝ))) ≤ |Real.log (Real.log (b : ℝ))| := by
          simpa using (neg_le_abs (Real.log (Real.log (b : ℝ))))
        have hlogbnonneg : (0 : ℝ) ≤ Real.log (b : ℝ) := le_of_lt hlogbpos
        have hdiv_neg_le : (-(Real.log (Real.log (b : ℝ)))) / Real.log (b : ℝ)
            ≤ |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) :=
          div_le_div_of_nonneg_right hneg_le_abs hlogbnonneg
        -- Now do the algebra by rewriting (a - b)/c as a/c + (-b)/c
        -- and then applying monotonicity on the constant part.
        --
        -- (We use `calc` with a final `linarith` on numerals only.)
        calc
          (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ))) / Real.log (b : ℝ) + 1
              = Real.log (Real.log (x : ℝ)) / Real.log (b : ℝ)
                  + (-(Real.log (Real.log (b : ℝ)))) / Real.log (b : ℝ) + 1 := by
                    -- distribute division over addition
                    ring
          _ ≤ Real.log (Real.log (x : ℝ)) / Real.log (b : ℝ)
                  + |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) + 1 := by
                    -- replace the constant term using hdiv_neg_le
                    have := add_le_add_left hdiv_neg_le (Real.log (Real.log (x : ℝ)) / Real.log (b : ℝ))
                    -- add 1 to both sides
                    have := add_le_add_right this 1
                    -- rearrange
                    simpa [add_assoc, add_left_comm, add_comm] using this
          _ ≤ Real.log (Real.log (x : ℝ)) / Real.log (b : ℝ)
                  + |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) + 2 := by
                    linarith
          _ = (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) +
                  (|Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) + 2) := by
                    -- rewrite division as multiplication by 1/log
                    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_assoc, add_left_comm, add_comm]
          _ = (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + C := by
                    simp [C, add_assoc]
      exact le_trans hncard_le hlogb_le
    -- Step 2: absorb the additive constant using L0 ≤ loglog x
    have hCnonneg : (0 : ℝ) ≤ C := by
      have hlogbnonneg : (0 : ℝ) ≤ Real.log (b : ℝ) := le_of_lt hlogbpos
      have hdiv_nonneg : (0 : ℝ) ≤ |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) :=
        div_nonneg (abs_nonneg _) hlogbnonneg
      have : (0 : ℝ) ≤ |Real.log (Real.log (b : ℝ))| / Real.log (b : ℝ) + 2 := by
        linarith
      simpa [C] using this
    have hCdiv_nonneg : (0 : ℝ) ≤ C / L0 := by
      exact div_nonneg hCnonneg (le_of_lt hL0pos)
    have hC_le : C ≤ (C / L0) * Real.log (Real.log (x : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hL0le hCdiv_nonneg
      -- simplify (C/L0)*L0 = C
      have hL0ne : (L0 : ℝ) ≠ 0 := ne_of_gt hL0pos
      -- rewrite the left side
      simpa [div_eq_mul_inv, mul_assoc, hL0ne] using hmul
    -- finish
    have : ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ)
        ≤ d2 * Real.log (Real.log (x : ℝ)) := by
      -- use hbound1 and then replace +C by *(C/L0)*loglog x
      have hloglogpos' : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := hloglogpos
      -- combine
      calc
        ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ)
            ≤ (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + C := hbound1
        _ ≤ (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + (C / L0) * Real.log (Real.log (x : ℝ)) := by
              -- add (1/logb)*loglog x to both sides of hC_le
              have := add_le_add_left hC_le ((1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)))
              simpa [add_assoc, add_left_comm, add_comm, mul_assoc] using this
        _ = ((1 / Real.log (b : ℝ)) + C / L0) * Real.log (Real.log (x : ℝ)) := by
              ring
        _ = d2 * Real.log (Real.log (x : ℝ)) := by
              simp [d2]
    -- cast back to the original goal (with implicit coercions)
    simpa using this

theorem theorem5_part1_density (b : ℕ) (hb : 2 ≤ b) :
  ∃ (d1 d2 : ℝ),
    ∀ (x : ℕ), x ≥ b ^ b →
      0 < d1 ∧ 0 < d2 ∧
        d1 * Real.log (Real.log x) ≤ (DoublyMacroSet b ∩ Ball x (A 1)).ncard ∧
        (DoublyMacroSet b ∩ Ball x (A 1)).ncard ≤ d2 * Real.log (Real.log x) := by
  classical
  rcases theorem5_part1_density_lower b hb with ⟨d1, hd1pos, hd1⟩
  rcases theorem5_part1_density_upper b hb with ⟨d2, hd2pos, hd2⟩
  refine ⟨d1, d2, ?_⟩
  intro x hx
  exact ⟨hd1pos, hd2pos, hd1 x hx, hd2 x hx⟩


theorem theorem5_part2_lower_nat (b : ℕ) (hb : 2 ≤ b) :
  ∃ C₂ : ℝ,
    0 < C₂ ∧
      ∀ s : ℕ, s ≥ 1 →
        let rs := Real.rpow s ((b : ℝ) / (b - 1))
        ∃ n : ℕ,
          n ≤ Int.toNat (Int.floor (C₂ * (s : ℝ) * rs)) ∧
            ¬ theorem5_Rep b s n := by
  classical
  refine ⟨(b : ℝ) + 3, ?_, ?_⟩
  · have hb0 : (0 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (Nat.zero_le b)
    linarith
  · intro s hs
    dsimp
    set rs : ℝ := Real.rpow s ((b : ℝ) / (b - 1)) with hrs
    let P : ℕ → Prop := fun k => s < (dblMacroVal b k) ^ (b - 1)
    have hex : ∃ k, P k := by
      simpa [P] using (exists_k_dblMacroVal_pow_gt b s hb)
    let k : ℕ := Nat.find hex
    have hk : P k := Nat.find_spec hex
    let m : ℕ := dblMacroVal b k
    let n : ℕ := s * m + 1
    refine ⟨n, ?_, ?_⟩
    · -- size bound
      have hs1_real : (1 : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast hs
      have hbsubpos : (0 : ℝ) < (b : ℝ) - 1 := by
        have hb1 : (1 : ℝ) < (b : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb)
        linarith
      have hz_nonneg : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := by
        have hbnonneg : (0 : ℝ) ≤ (b : ℝ) := by positivity
        have hden : (0 : ℝ) ≤ (b : ℝ) - 1 := le_of_lt hbsubpos
        exact div_nonneg hbnonneg hden
      have hrs_ge1 : (1 : ℝ) ≤ rs := by
        rw [hrs]
        exact Real.one_le_rpow hs1_real hz_nonneg

      have hn_le_x : (n : ℝ) ≤ ((b : ℝ) + 3) * (s : ℝ) * rs := by
        by_cases hk0 : k = 0
        · have h1 : (1 : ℝ) ≤ (3 : ℝ) * (s : ℝ) := by
            nlinarith [hs1_real]
          have hn_le_base : (n : ℝ) ≤ ((b : ℝ) + 3) * (s : ℝ) := by
            -- n = s*b + 1
            simp [n, m, k, hk0, dblMacroVal]
            nlinarith [h1]
          have hfac_nonneg : (0 : ℝ) ≤ ((b : ℝ) + 3) * (s : ℝ) := by positivity
          have hmul : ((b : ℝ) + 3) * (s : ℝ) ≤ ((b : ℝ) + 3) * (s : ℝ) * rs := by
            simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hrs_ge1 hfac_nonneg)
          exact le_trans hn_le_base hmul
        · -- k ≠ 0
          have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
          have hk1 : 1 ≤ k := Nat.succ_le_iff.2 hk_pos
          set j : ℕ := k - 1 with hj
          have hjlt : j < k := by omega
          have hkmin : ¬ P j := by
            have : j < Nat.find hex := by
              simpa [k] using hjlt
            exact Nat.find_min hex this
          have hj_pow_le_nat : (dblMacroVal b j) ^ (b - 1) ≤ s := (not_lt).1 hkmin
          have hj_pow_le_real : ((dblMacroVal b j : ℝ) ^ (b - 1)) ≤ (s : ℝ) := by
            exact_mod_cast hj_pow_le_nat
          -- set A = dblMacroVal b j as real
          set A : ℝ := (dblMacroVal b j : ℝ)
          have hA_nonneg : 0 ≤ A := by positivity [A]
          have hx0 : 0 ≤ A ^ (b - 1) := by positivity
          have h_rpow : (A ^ (b - 1)) ^ ((b : ℝ) / ((b : ℝ) - 1)) ≤
              (s : ℝ) ^ ((b : ℝ) / ((b : ℝ) - 1)) :=
            Real.rpow_le_rpow hx0 (by simpa [A] using hj_pow_le_real) hz_nonneg
          have hpow : (A ^ (b - 1)) ^ ((b : ℝ) / ((b : ℝ) - 1)) =
              A ^ (((b - 1 : ℕ) : ℝ) * ((b : ℝ) / ((b : ℝ) - 1))) := by
            simpa [A] using
              (Real.rpow_natCast_mul (x := A) (hx := hA_nonneg) (n := b - 1)
                (z := (b : ℝ) / ((b : ℝ) - 1))).symm
          have h_rpow' : A ^ (((b - 1 : ℕ) : ℝ) * ((b : ℝ) / ((b : ℝ) - 1))) ≤
              (s : ℝ) ^ ((b : ℝ) / ((b : ℝ) - 1)) := by
            simpa [hpow] using h_rpow
          have hb1_nat : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
          have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
            simpa using (Nat.cast_sub (R := ℝ) (m := 1) (n := b) hb1_nat)
          have hExp : ((b - 1 : ℕ) : ℝ) * ((b : ℝ) / ((b : ℝ) - 1)) = (b : ℝ) := by
            have hden : (b : ℝ) - 1 ≠ 0 := ne_of_gt hbsubpos
            calc
              ((b - 1 : ℕ) : ℝ) * ((b : ℝ) / ((b : ℝ) - 1))
                  = ((b : ℝ) - 1) * ((b : ℝ) / ((b : ℝ) - 1)) := by
                    simpa [hcast]
              _ = (b : ℝ) := by
                field_simp [hden]
          have h_rpow'' : A ^ (b : ℝ) ≤ (s : ℝ) ^ ((b : ℝ) / ((b : ℝ) - 1)) := by
            simpa [hExp] using h_rpow'
          have hA_pow_le : A ^ b ≤ (s : ℝ) ^ ((b : ℝ) / ((b : ℝ) - 1)) := by
            simpa [Real.rpow_natCast A b] using h_rpow''
          -- relate m and A^b
          have hk_eq : k = j + 1 := by
            have : j + 1 = k := by
              simpa [j, hj] using (Nat.sub_add_cancel hk1)
            simpa using this.symm
          have hm_eq : m = (dblMacroVal b j) ^ b := by
            calc
              m = dblMacroVal b k := by rfl
              _ = dblMacroVal b (j + 1) := by simpa [hk_eq]
              _ = (dblMacroVal b j) ^ b := by
                simpa using (dblMacroVal_succ_eq_pow b j)
          have hm_eq_real : (m : ℝ) = A ^ b := by
            -- cast hm_eq and unfold A
            have : (m : ℝ) = (dblMacroVal b j : ℝ) ^ b := by
              exact_mod_cast hm_eq
            simpa [A] using this
          have hm_le_rs : (m : ℝ) ≤ rs := by
            -- use hA_pow_le and hrs
            have : (m : ℝ) ≤ (s : ℝ) ^ ((b : ℝ) / ((b : ℝ) - 1)) := by
              -- rewrite hm_eq_real
              simpa [hm_eq_real] using hA_pow_le
            simpa [hrs] using this
          have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by positivity
          have hmul : (s : ℝ) * (m : ℝ) ≤ (s : ℝ) * rs :=
            mul_le_mul_of_nonneg_left hm_le_rs hs_nonneg
          have hn_le_sr : (n : ℝ) ≤ (s : ℝ) * rs + 1 := by
            -- rewrite n
            have : (n : ℝ) = (s : ℝ) * (m : ℝ) + 1 := by
              simp [n]
            --
            -- use hmul
            --
            nlinarith [this, hmul]
          have hsrs_ge1 : (1 : ℝ) ≤ (s : ℝ) * rs := by
            nlinarith [hs1_real, hrs_ge1]
          have hb2_ge1 : (1 : ℝ) ≤ (b : ℝ) + 2 := by
            have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
            linarith
          have hsr1_le : (s : ℝ) * rs + 1 ≤ ((b : ℝ) + 3) * (s : ℝ) * rs := by
            -- linear inequality
            nlinarith [hsrs_ge1, hb2_ge1]
          exact le_trans hn_le_sr hsr1_le

      -- convert to floor
      have hn_int : (n : ℤ) ≤ Int.floor (((b : ℝ) + 3) * (s : ℝ) * rs) := by
        exact (Int.le_floor).2 (by simpa using hn_le_x)
      have hfloor_nonneg : 0 ≤ Int.floor (((b : ℝ) + 3) * (s : ℝ) * rs) := by
        have hx0' : (0 : ℝ) ≤ ((b : ℝ) + 3) * (s : ℝ) * rs := by
          have : (0 : ℝ) ≤ rs := le_trans (by linarith) hrs_ge1
          positivity
        exact (Int.le_floor).2 (by simpa using hx0')
      have hz' : (Int.toNat (Int.floor (((b : ℝ) + 3) * (s : ℝ) * rs)) : ℤ) =
          Int.floor (((b : ℝ) + 3) * (s : ℝ) * rs) := by
        simpa using (Int.toNat_of_nonneg hfloor_nonneg)
      have hn_int' : (n : ℤ) ≤ (Int.toNat (Int.floor (((b : ℝ) + 3) * (s : ℝ) * rs)) : ℤ) := by
        simpa [hz'] using hn_int
      exact Int.le_of_ofNat_le_ofNat hn_int'

    · -- not representable
      intro hRep
      rcases hRep with ⟨l, hl_len, hl_coin, hl_sum⟩
      have hk' : s < m ^ (b - 1) := by
        simpa [P, k, m] using hk
      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
      have hm1 : 1 < m := by
        have hb_lt : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
        have hb0' : b ≠ 0 := by
          exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb)
        have hk_ne : b ^ k ≠ 0 := pow_ne_zero k hb0'
        have : 1 < b ^ (b ^ k) := one_lt_pow' hb_lt hk_ne
        simpa [m, dblMacroVal] using this
      have hs_succ_le : s + 1 ≤ m ^ (b - 1) := Nat.succ_le_of_lt hk'
      have hmul1 : (s + 1) * m ≤ (m ^ (b - 1)) * m := Nat.mul_le_mul_right m hs_succ_le
      have hmul2 : (s + 1) * m ≤ m ^ b := by
        have : (m ^ (b - 1)) * m = m ^ b := by
          calc
            (m ^ (b - 1)) * m = m ^ ((b - 1) + 1) := by
              simpa using (pow_succ m (b - 1)).symm
            _ = m ^ b := by
              simpa [Nat.sub_add_cancel hb1]
        simpa [this] using hmul1
      have hn_lt_pow : n < m ^ b := by
        have hlt1 : s * m + 1 < s * m + m := by
          exact Nat.add_lt_add_left hm1 (s * m)
        have hle1 : s * m + m ≤ m ^ b := by
          have := hmul2
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
        exact lt_of_lt_of_le hlt1 hle1
      have hn_lt_dbl : n < dblMacroVal b (k + 1) := by
        have : m ^ b = dblMacroVal b (k + 1) := by
          simpa [m] using (dblMacroVal_succ_eq_pow b k).symm
        simpa [this] using hn_lt_pow
      have hbound : ∀ t ∈ l, t ≤ m := by
        intro t ht
        have ht_le_sum : t ≤ l.sum := List.le_sum_of_mem ht
        have ht_le_n : t ≤ n := by
          simpa [hl_sum] using ht_le_sum
        have ht_lt_dbl : t < dblMacroVal b (k + 1) := lt_of_le_of_lt ht_le_n hn_lt_dbl
        have htcoin : theorem5_coinPred b t := hl_coin t ht
        rcases htcoin with rfl | ⟨j, rfl⟩
        · exact Nat.le_of_lt hm1
        · have hj : j ≤ k := by
            have hjlt : j < k + 1 := by
              by_contra hge
              have hge' : k + 1 ≤ j := le_of_not_gt hge
              have hle : dblMacroVal b (k + 1) ≤ dblMacroVal b j :=
                dblMacroVal_mono b (k + 1) j hb hge'
              exact (not_lt_of_ge hle) ht_lt_dbl
            exact Nat.lt_succ_iff.mp hjlt
          have : dblMacroVal b j ≤ dblMacroVal b k := dblMacroVal_mono b j k hb hj
          simpa [m] using this
      have hsum_le_nsmul : l.sum ≤ l.length • m := List.sum_le_card_nsmul l m hbound
      have hsum_le_mul : l.sum ≤ l.length * m := by
        simpa [Nat.nsmul_eq_mul] using hsum_le_nsmul
      have hsum_le_sm : l.sum ≤ s * m := le_trans hsum_le_mul (Nat.mul_le_mul_right m hl_len)
      have hnle : n ≤ s * m := by
        simpa [hl_sum] using hsum_le_sm
      have : s * m + 1 ≤ s * m := by
        simpa [n] using hnle
      exact (Nat.not_succ_le_self (s * m)) this


theorem theorem5_part2_lower (b : ℕ) (hb : 2 ≤ b) :
  ∃ C₂ : ℝ,
    0 < C₂ ∧
      ∀ s : ℕ, s ≥ 1 →
        let rs := Real.rpow s ((b : ℝ) / (b - 1))
        ¬ (Ball (Int.toNat (Int.floor (C₂ * (s : ℝ) * rs))) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1)) := by
  classical
  rcases theorem5_part2_lower_nat b hb with ⟨C₂, hC₂pos, hGap⟩
  refine ⟨C₂, hC₂pos, ?_⟩
  intro s hs
  dsimp
  have hGap' := hGap s hs
  dsimp at hGap'
  rcases hGap' with ⟨n, hnle, hnnot⟩
  -- witness multiset with card = n
  let m : FreeAbelianMonoid 1 := Multiset.replicate n (0 : Fin 1)
  refine (Set.not_subset).2 ?_
  refine ⟨m, ?_, ?_⟩
  · -- m in the left ball
    have hmle : m.card ≤ Int.toNat (Int.floor (C₂ * (s : ℝ) * Real.rpow s ((b : ℝ) / (b - 1)))) := by
      simpa [m] using hnle
    exact (ball_A1_mem_iff_card_le (Int.toNat (Int.floor (C₂ * (s : ℝ) * Real.rpow s ((b : ℝ) / (b - 1))))) m).2 hmle
  · -- m not in the right ball
    intro hmBall
    rcases (ball_macro_union_mem_iff_coinList b s m).1 hmBall with ⟨l, hl, hcoins, hsum⟩
    exact hnnot ⟨l, hl, hcoins, by simpa [m] using hsum⟩


theorem theorem5_pow_rpow_inv_nat (x : ℝ) (n : ℕ) : 0 ≤ x → n ≠ 0 → (x ^ n) ^ ((n : ℝ)⁻¹) = x := by
  intro hx hn
  simpa using (Real.pow_rpow_inv_natCast (x := x) (n := n) hx hn)


theorem theorem5_rpow_dblMacroVal_eq_succ (b k : ℕ) : Real.rpow (dblMacroVal b k : ℝ) (b : ℝ) = (dblMacroVal b (k + 1) : ℝ) := by
  -- rewrite the real power with a natural exponent
  change (dblMacroVal b k : ℝ) ^ (b : ℝ) = (dblMacroVal b (k + 1) : ℝ)
  -- convert the real exponent `(b : ℝ)` to a natural power
  rw [Real.rpow_natCast]
  -- use the defining recursion for `dblMacroVal`
  -- and cast the natural power to `ℝ`
  simpa [dblMacroVal_succ_eq_pow] using congrArg (fun n : ℕ => (n : ℝ)) (dblMacroVal_succ_eq_pow b k).symm

theorem theorem5_rpow_lt_of_pow_nat_lt (x y : ℝ) (n : ℕ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) : x < y ^ n → x ^ ((n : ℝ)⁻¹) < y := by
  intro h
  have hn_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hn_real : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_nat
  have hz : 0 < ((n : ℝ)⁻¹) := by
    exact (inv_pos).2 hn_real
  have h' : x ^ ((n : ℝ)⁻¹) < (y ^ n) ^ ((n : ℝ)⁻¹) := by
    exact Real.rpow_lt_rpow hx h hz
  simpa [theorem5_pow_rpow_inv_nat y n hy hn] using h'

theorem theorem5_rpow_rpow_natCast (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (n : ℕ) : (x ^ a) ^ (n : ℝ) = x ^ (a * (n : ℝ)) := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using (Real.rpow_mul (x := x) hx a (n : ℝ)).symm

theorem theorem5_rpow_two_le_16 (b : ℕ) (hb : 2 ≤ b) : Real.rpow (4 : ℝ) ((b : ℝ) / (b - 1)) ≤ 16 := by
  have hp : ((b : ℝ) / (b - 1)) ≤ (2 : ℝ) := theorem5_exp_le_two b hb
  have hbase : (1 : ℝ) ≤ (4 : ℝ) := by
    norm_num
  have h := Real.rpow_le_rpow_of_exponent_le hbase hp
  have h16 : (4 : ℝ) ^ (2 : ℝ) = (16 : ℝ) := by
    -- rewrite real power with exponent 2 as a natural square
    calc
      (4 : ℝ) ^ (2 : ℝ) = (4 : ℝ) ^ (2 : ℕ) := by
        simpa using (Real.rpow_two (4 : ℝ))
      _ = (16 : ℝ) := by
        norm_num
  have h' : (4 : ℝ) ^ ((b : ℝ) / (b - 1)) ≤ (16 : ℝ) := by
    calc
      (4 : ℝ) ^ ((b : ℝ) / (b - 1)) ≤ (4 : ℝ) ^ (2 : ℝ) := h
      _ = (16 : ℝ) := h16
  simpa using h'

theorem theorem5_one_div_16_mul_rpow_le_rpow_div_four (b : ℕ) (hb : 2 ≤ b) (s : ℝ) : 0 ≤ s → ((1 : ℝ) / 16) * Real.rpow s ((b : ℝ) / (b - 1)) ≤ Real.rpow (s / 4) ((b : ℝ) / (b - 1)) := by
  intro hs
  set p : ℝ := (b : ℝ) / (b - 1)
  have hdiv : Real.rpow (s / 4) p = Real.rpow s p / Real.rpow (4 : ℝ) p := by
    simpa [p] using (Real.div_rpow hs (by positivity : 0 ≤ (4 : ℝ)) p)
  have hA : 0 ≤ Real.rpow s p := by
    exact Real.rpow_nonneg hs _
  have h4pos : 0 < Real.rpow (4 : ℝ) p := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have h4le : Real.rpow (4 : ℝ) p ≤ 16 := by
    simpa [p] using theorem5_rpow_two_le_16 b hb
  have hcoeff : (1 : ℝ) / 16 ≤ (1 : ℝ) / Real.rpow (4 : ℝ) p := by
    -- a ≤ b => 1/b ≤ 1/a
    simpa [one_div] using (one_div_le_one_div_of_le h4pos h4le)
  -- rewrite RHS using hdiv
  rw [hdiv]
  -- multiply inequality by nonnegative Real.rpow s p
  have := mul_le_mul_of_nonneg_left hcoeff hA
  -- massage into desired form
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

theorem theorem5_rpow_two_le_4 (b : ℕ) (hb : 2 ≤ b) : Real.rpow (2 : ℝ) ((b : ℝ) / (b - 1)) ≤ 4 := by
  have hbexp : (b : ℝ) / (b - 1) ≤ 2 := theorem5_exp_le_two b hb
  have h : (2 : ℝ) ^ ((b : ℝ) / (b - 1)) ≤ (2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hbexp
  have h2 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by
    -- rewrite the real exponent as a natural exponent
    simpa [Real.rpow_natCast] using (show (2 : ℝ) ^ (2 : ℕ) = (4 : ℝ) by norm_num)
  -- finish
  simpa [h2] using h

theorem theorem5_one_div_16_mul_rpow_le_rpow_div_two (b : ℕ) (hb : 2 ≤ b) (s : ℝ) : (0 ≤ s) → ((1 : ℝ) / 16) * (Real.rpow s ((b : ℝ) / (b - 1))) ≤ Real.rpow (s / 2) ((b : ℝ) / (b - 1)) := by
  intro hs
  -- set the exponent
  set p : ℝ := (b : ℝ) / (b - 1)
  have hdiv : Real.rpow (s / 2) p = Real.rpow s p / Real.rpow (2 : ℝ) p := by
    -- use (x / y)^z = x^z / y^z for nonnegative x,y
    simpa [Real.rpow_def] using (Real.div_rpow (x := s) (y := (2 : ℝ)) hs (by positivity : (0 : ℝ) ≤ (2 : ℝ)) p)
  -- rewrite the goal using hdiv
  rw [hdiv]
  -- show that 2^p ≤ 16
  have htwo_le : Real.rpow (2 : ℝ) p ≤ 16 := by
    have htwo_le4 : Real.rpow (2 : ℝ) p ≤ 4 := theorem5_rpow_two_le_4 b hb
    have h4le16 : (4 : ℝ) ≤ 16 := by norm_num
    exact le_trans htwo_le4 h4le16
  have htwo_pos : 0 < Real.rpow (2 : ℝ) p := by
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.rpow_pos_of_pos h2pos p
  have hfrac : (1 : ℝ) / 16 ≤ (1 : ℝ) / Real.rpow (2 : ℝ) p := by
    -- reciprocal reverses inequality for positive numbers
    simpa [one_div] using (one_div_le_one_div_of_le htwo_pos htwo_le)
  have hs_pow : 0 ≤ Real.rpow s p := by
    exact Real.rpow_nonneg hs p
  -- multiply the inequality hfrac by s^p
  have hmul : ((1 : ℝ) / 16) * Real.rpow s p ≤ ((1 : ℝ) / Real.rpow (2 : ℝ) p) * Real.rpow s p := by
    exact mul_le_mul_of_nonneg_right hfrac hs_pow
  -- conclude by rewriting division
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem theorem5_same_add_div_one (d : ℝ) (hd : d ≠ 0) : (d + 1) / d = (1 : ℝ) + d⁻¹ := by
  simpa [one_div] using (same_add_div (a := (1:ℝ)) (b := d) hd)

theorem theorem5_exp_eq_one_add_inv (b : ℕ) (hb : 2 ≤ b) : ((b : ℝ) / (b - 1)) = (1 : ℝ) + (((b - 1 : ℕ) : ℝ)⁻¹) := by
  -- follow the suggested intermediate form with d := ((b - 1 : ℕ) : ℝ)
  have hb1 : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hd : ((b - 1 : ℕ) : ℝ) ≠ 0 := by
    have hbpos : (0 : ℕ) < b - 1 := by
      omega
    have hbposR : (0 : ℝ) < ((b - 1 : ℕ) : ℝ) := by
      exact_mod_cast hbpos
    exact ne_of_gt hbposR
  have hb_eq : (b : ℝ) = ((b - 1 : ℕ) : ℝ) + 1 := by
    have hsub : b - 1 + 1 = b := Nat.sub_add_cancel hb1
    have hsub' : ((b - 1 + 1 : ℕ) : ℝ) = (b : ℝ) := by
      exact_mod_cast hsub
    -- rewrite the cast of (b - 1 + 1) as cast (b - 1) + 1
    simpa [Nat.cast_add, Nat.cast_one] using hsub'.symm
  -- rewrite numerator using hb_eq and apply theorem5_same_add_div_one
  rw [hb_eq]
  simpa using (theorem5_same_add_div_one ((b - 1 : ℕ) : ℝ) hd)

theorem theorem5_exists_scaledMacro_radius_caseA (b : ℕ) (hb : 2 ≤ b) (s k : ℕ)
  (hkT : theorem5_T b k ≤ s)
  (hs_sub : s - theorem5_T b k < (dblMacroVal b k : ℝ) ^ (b - 1))
  (hsmall : (theorem5_T b k : ℝ) ≤ (s : ℝ) / 2) :
  ((1 : ℝ) / 16) * Real.rpow s ((b : ℝ) / (b - 1)) ≤
    ((s - theorem5_T b k + 1) * dblMacroVal b k : ℝ) := by
  classical
  set T : ℕ := theorem5_T b k
  set m : ℕ := dblMacroVal b k

  have hkT' : T ≤ s := by
    simpa [T] using hkT

  have hsubR : (s : ℝ) - (T : ℝ) < (m : ℝ) ^ (b - 1) := by
    simpa [T, m] using hs_sub

  have hsmall' : (T : ℝ) ≤ (s : ℝ) / 2 := by
    simpa [T] using hsmall

  have hhalf_le : (s : ℝ) / 2 ≤ (s : ℝ) - (T : ℝ) := by
    linarith

  have hhalf_lt_pow : (s : ℝ) / 2 < (m : ℝ) ^ (b - 1) := lt_of_le_of_lt hhalf_le hsubR

  have hb1_ne : (b - 1) ≠ 0 := by
    omega

  have hroot_lt : ((s : ℝ) / 2) ^ (((b - 1 : ℕ) : ℝ)⁻¹) < (m : ℝ) := by
    have hx : 0 ≤ (s : ℝ) / 2 := by positivity
    have hy : 0 ≤ (m : ℝ) := by positivity
    exact theorem5_rpow_lt_of_pow_nat_lt ((s : ℝ) / 2) (m : ℝ) (b - 1) hx hy hb1_ne hhalf_lt_pow

  have hfac : (s : ℝ) / 2 ≤ (s - T + 1 : ℝ) := by
    have hcast : (s - T + 1 : ℝ) = (s : ℝ) - (T : ℝ) + 1 := by
      simp [Nat.cast_add, Nat.cast_one, Nat.cast_sub hkT', add_assoc, add_comm, add_left_comm, sub_eq_add_neg]
    linarith [hhalf_le, hcast]

  have hprod : (s : ℝ) / 2 * (((s : ℝ) / 2) ^ (((b - 1 : ℕ) : ℝ)⁻¹)) ≤ (s - T + 1 : ℝ) * (m : ℝ) := by
    have hx0 : 0 ≤ (s : ℝ) / 2 := by positivity
    have hy0 : 0 ≤ ((s : ℝ) / 2) ^ (((b - 1 : ℕ) : ℝ)⁻¹) := by
      exact Real.rpow_nonneg hx0 _
    have hroot_le : ((s : ℝ) / 2) ^ (((b - 1 : ℕ) : ℝ)⁻¹) ≤ (m : ℝ) := le_of_lt hroot_lt
    have hb0 : 0 ≤ (s - T + 1 : ℝ) := by
      exact_mod_cast (Nat.zero_le (s - T + 1))
    exact mul_le_mul hfac hroot_le hy0 hb0

  have hs0 : 0 ≤ (s : ℝ) := by positivity

  have hL : ((1 : ℝ) / 16) * Real.rpow (s : ℝ) ((b : ℝ) / (b - 1)) ≤
      Real.rpow ((s : ℝ) / 2) ((b : ℝ) / (b - 1)) :=
    theorem5_one_div_16_mul_rpow_le_rpow_div_two b hb (s : ℝ) hs0

  have hexp : ((b : ℝ) / (b - 1)) = (1 : ℝ) + (((b - 1 : ℕ) : ℝ)⁻¹) := theorem5_exp_eq_one_add_inv b hb

  have hrpow_decomp :
      Real.rpow ((s : ℝ) / 2) ((b : ℝ) / (b - 1)) =
        (s : ℝ) / 2 * Real.rpow ((s : ℝ) / 2) (((b - 1 : ℕ) : ℝ)⁻¹) := by
    have hs2_nonneg : 0 ≤ (s : ℝ) / 2 := by positivity
    have hinv_nonneg : 0 ≤ (((b - 1 : ℕ) : ℝ)⁻¹) := by
      apply inv_nonneg_of_nonneg
      exact_mod_cast (Nat.zero_le (b - 1))
    calc
      Real.rpow ((s : ℝ) / 2) ((b : ℝ) / (b - 1))
          = ((s : ℝ) / 2) ^ ((1 : ℝ) + (((b - 1 : ℕ) : ℝ)⁻¹)) := by
              simpa [Real.rpow_def, hexp]
      _ = ((s : ℝ) / 2) ^ (1 : ℝ) * ((s : ℝ) / 2) ^ (((b - 1 : ℕ) : ℝ)⁻¹) := by
              -- split exponent
              simpa using
                (Real.rpow_add_of_nonneg (x := (s : ℝ) / 2) (y := (1 : ℝ))
                  (z := (((b - 1 : ℕ) : ℝ)⁻¹)) hs2_nonneg (by linarith) hinv_nonneg)
      _ = (s : ℝ) / 2 * Real.rpow ((s : ℝ) / 2) (((b - 1 : ℕ) : ℝ)⁻¹) := by
              simp [Real.rpow_one]

  have hmid : Real.rpow ((s : ℝ) / 2) ((b : ℝ) / (b - 1)) ≤ (s - T + 1 : ℝ) * (m : ℝ) := by
    -- rewrite LHS and apply hprod
    rw [hrpow_decomp]
    -- hprod uses `^` notation; rewrite
    simpa using hprod

  calc
    ((1 : ℝ) / 16) * Real.rpow (s : ℝ) ((b : ℝ) / (b - 1))
        ≤ Real.rpow ((s : ℝ) / 2) ((b : ℝ) / (b - 1)) := hL
    _ ≤ (s - T + 1 : ℝ) * (m : ℝ) := hmid
    _ = ((s - T + 1) * m : ℝ) := by
          norm_cast
    _ = ((s - theorem5_T b k + 1) * dblMacroVal b k : ℝ) := by
          simp [T, m]


theorem theorem5_rpow_decomp (b : ℕ) (hb : 2 ≤ b) (x : ℝ) : 0 ≤ x → Real.rpow x ((b : ℝ) / (b - 1)) = x * Real.rpow x (((b - 1 : ℕ) : ℝ)⁻¹) := by
  intro hx
  let inv : ℝ := (((b - 1 : ℕ) : ℝ)⁻¹)
  have hexp : ((b : ℝ) / (b - 1)) = (1 : ℝ) + inv := by
    simpa [inv] using theorem5_exp_eq_one_add_inv b hb
  rw [hexp]
  have hinv : 0 ≤ inv := by
    dsimp [inv]
    positivity
  have h := Real.rpow_add_of_nonneg hx (by positivity : (0 : ℝ) ≤ (1 : ℝ)) hinv
  -- h : x ^ ((1 : ℝ) + inv) = x ^ (1 : ℝ) * x ^ inv
  simpa [Real.rpow_one, mul_assoc] using h

theorem theorem5_exists_scaledMacro_radius_caseB (b : ℕ) (hb : 2 ≤ b) (s k : ℕ)
  (hkT : theorem5_T b k ≤ s)
  (hlarge : (s : ℝ) / 2 < (theorem5_T b k : ℝ)) :
  ((1 : ℝ) / 16) * Real.rpow s ((b : ℝ) / (b - 1)) ≤
    ((s - theorem5_T b k + 1) * dblMacroVal b k : ℝ) := by
  classical
  have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by
    positivity
  have hscale : ((1 : ℝ) / 16) * Real.rpow (s : ℝ) ((b : ℝ) / (b - 1)) ≤
      Real.rpow ((s : ℝ) / 4) ((b : ℝ) / (b - 1)) :=
    theorem5_one_div_16_mul_rpow_le_rpow_div_four b hb (s : ℝ) hs_nonneg
  have hmain : Real.rpow ((s : ℝ) / 4) ((b : ℝ) / (b - 1)) ≤
      ((s - theorem5_T b k + 1) * dblMacroVal b k : ℝ) := by
    have hcoeff_nat : 1 ≤ s - theorem5_T b k + 1 := by
      exact Nat.succ_le_succ (Nat.zero_le _)
    have hcoeff : (1 : ℝ) ≤ (s - theorem5_T b k + 1 : ℝ) := by
      exact_mod_cast hcoeff_nat
    have hnonneg_mk : (0 : ℝ) ≤ (dblMacroVal b k : ℝ) := by
      positivity
    have hmul_mk : (dblMacroVal b k : ℝ) ≤ ((s - theorem5_T b k + 1) * dblMacroVal b k : ℝ) := by
      simpa [one_mul] using (mul_le_mul_of_nonneg_right hcoeff hnonneg_mk)
    have hbound : Real.rpow ((s : ℝ) / 4) ((b : ℝ) / (b - 1)) ≤ (dblMacroVal b k : ℝ) := by
      cases k with
      | zero =>
          have hs4_nonneg : (0 : ℝ) ≤ (s : ℝ) / 4 := by positivity
          have hb1_ne : (b - 1 : ℕ) ≠ 0 := by omega
          have hs2_lt_b1 : (s : ℝ) / 2 < ((b - 1 : ℕ) : ℝ) := by
            simpa [theorem5_T] using hlarge
          have hs4_lt_b1 : (s : ℝ) / 4 < ((b - 1 : ℕ) : ℝ) := by
            linarith
          have hs4_lt : (s : ℝ) / 4 < (2 : ℝ) ^ (b - 1) := by
            have hb1_le_pow : ((b - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (b - 1) := by
              exact theorem5_bsub1_le_two_pow_real b
            exact lt_of_lt_of_le hs4_lt_b1 hb1_le_pow
          have hroot_lt : Real.rpow ((s : ℝ) / 4) (((b - 1 : ℕ) : ℝ)⁻¹) < (2 : ℝ) := by
            have h2_nonneg : (0 : ℝ) ≤ (2 : ℝ) := by positivity
            have htmp := theorem5_rpow_lt_of_pow_nat_lt ((s : ℝ) / 4) (2 : ℝ) (b - 1)
              hs4_nonneg h2_nonneg hb1_ne hs4_lt
            simpa using htmp
          have hroot_le : Real.rpow ((s : ℝ) / 4) (((b - 1 : ℕ) : ℝ)⁻¹) ≤ (2 : ℝ) :=
            le_of_lt hroot_lt
          have hpow_eq : Real.rpow ((s : ℝ) / 4) ((b : ℝ) / (b - 1)) =
              ((s : ℝ) / 4) * Real.rpow ((s : ℝ) / 4) (((b - 1 : ℕ) : ℝ)⁻¹) :=
            theorem5_rpow_decomp b hb ((s : ℝ) / 4) hs4_nonneg
          have hpow_le_s2 : Real.rpow ((s : ℝ) / 4) ((b : ℝ) / (b - 1)) ≤ (s : ℝ) / 2 := by
            have hmul_le : ((s : ℝ) / 4) * Real.rpow ((s : ℝ) / 4) (((b - 1 : ℕ) : ℝ)⁻¹) ≤
                ((s : ℝ) / 4) * 2 := by
              exact mul_le_mul_of_nonneg_left hroot_le (by positivity : (0 : ℝ) ≤ (s : ℝ) / 4)
            have hmul_le' : Real.rpow ((s : ℝ) / 4) ((b : ℝ) / (b - 1)) ≤ ((s : ℝ) / 4) * 2 := by
              rw [hpow_eq]
              exact hmul_le
            have hcalc : ((s : ℝ) / 4) * 2 = (s : ℝ) / 2 := by ring
            simpa [hcalc] using hmul_le'
          have hs2_lt_b : (s : ℝ) / 2 < (b : ℝ) := by
            have hb1_lt_b : ((b - 1 : ℕ) : ℝ) < (b : ℝ) := by
              have hb1 : 1 ≤ b := by omega
              have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := theorem5_cast_sub_one b hb1
              have : (b : ℝ) - 1 < (b : ℝ) := by linarith
              simpa [hcast] using this
            exact lt_trans hs2_lt_b1 hb1_lt_b
          have hs2_le_b : (s : ℝ) / 2 ≤ (b : ℝ) := le_of_lt hs2_lt_b
          have hpow_le_b : Real.rpow ((s : ℝ) / 4) ((b : ℝ) / (b - 1)) ≤ (b : ℝ) :=
            le_trans hpow_le_s2 hs2_le_b
          simpa [dblMacroVal] using hpow_le_b
      | succ k' =>
          have hk_pos : (1 : ℕ) ≤ Nat.succ k' := by omega
          have hTle_nat : theorem5_T b (Nat.succ k') ≤ 2 * (dblMacroVal b k') ^ (b - 1) := by
            simpa using (theorem5_T_le_two_last b hb (Nat.succ k') hk_pos)
          have hTle : (theorem5_T b (Nat.succ k') : ℝ) ≤ 2 * (dblMacroVal b k' : ℝ) ^ (b - 1) := by
            exact_mod_cast hTle_nat
          have hs4_lt : (s : ℝ) / 4 < (dblMacroVal b k' : ℝ) ^ (b - 1) := by
            have : (s : ℝ) / 2 < 2 * (dblMacroVal b k' : ℝ) ^ (b - 1) := lt_of_lt_of_le hlarge hTle
            linarith
          have hs4_nonneg : (0 : ℝ) ≤ (s : ℝ) / 4 := by positivity
          have hmk_nonneg : (0 : ℝ) ≤ (dblMacroVal b k' : ℝ) := by positivity
          have hb1_ne : (b - 1 : ℕ) ≠ 0 := by omega
          have hroot : ((s : ℝ) / 4) ^ (((b - 1 : ℕ) : ℝ)⁻¹) < (dblMacroVal b k' : ℝ) :=
            theorem5_rpow_lt_of_pow_nat_lt ((s : ℝ) / 4) (dblMacroVal b k' : ℝ) (b - 1)
              hs4_nonneg hmk_nonneg hb1_ne hs4_lt
          have hbpos : (0 : ℝ) < (b : ℝ) := by
            have : (0 : ℕ) < b := by omega
            exact_mod_cast this
          have hx0 : (0 : ℝ) ≤ ((s : ℝ) / 4) ^ (((b - 1 : ℕ) : ℝ)⁻¹) := by
            exact Real.rpow_nonneg hs4_nonneg _
          have hpow : (((s : ℝ) / 4) ^ (((b - 1 : ℕ) : ℝ)⁻¹)) ^ (b : ℕ) <
              (dblMacroVal b k' : ℝ) ^ (b : ℕ) := by
            -- start from rpow monotonicity, then simp to nat powers
            have hpow' : Real.rpow (((s : ℝ) / 4) ^ (((b - 1 : ℕ) : ℝ)⁻¹)) (b : ℝ) <
                Real.rpow (dblMacroVal b k' : ℝ) (b : ℝ) :=
              Real.rpow_lt_rpow hx0 hroot hbpos
            simpa using hpow'
          have hleft : (((s : ℝ) / 4) ^ (((b - 1 : ℕ) : ℝ)⁻¹)) ^ (b : ℕ) =
              ((s : ℝ) / 4) ^ ((((b - 1 : ℕ) : ℝ)⁻¹) * (b : ℝ)) := by
            have :=
              (theorem5_rpow_rpow_natCast ((s : ℝ) / 4) hs4_nonneg (((b - 1 : ℕ) : ℝ)⁻¹) b)
            -- rewrite outer rpow exponent (b:ℝ) as nat power
            simpa [Real.rpow_natCast, mul_assoc] using this
          have hpow_rewrite : ((s : ℝ) / 4) ^ ((((b - 1 : ℕ) : ℝ)⁻¹) * (b : ℝ)) <
              (dblMacroVal b k' : ℝ) ^ (b : ℕ) := by
            have h := hpow
            -- hleft : ((s/4)^inv)^b = (s/4)^(inv*(b:ℝ))
            -- so rewrite using hleft
            rw [hleft] at h
            exact h
          have hexp : (((b - 1 : ℕ) : ℝ)⁻¹) * (b : ℝ) = (b : ℝ) / (b - 1) := by
            exact theorem5_inv_mul_b_eq_div b
          have hRnat : (dblMacroVal b k' : ℝ) ^ (b : ℕ) = (dblMacroVal b (k' + 1) : ℝ) := by
            have h2 : dblMacroVal b (k' + 1) = (dblMacroVal b k') ^ b := dblMacroVal_succ_eq_pow b k'
            exact_mod_cast h2.symm
          have hrpow_lt : ((s : ℝ) / 4) ^ ((b : ℝ) / (b - 1)) < (dblMacroVal b (k' + 1) : ℝ) := by
            have h := hpow_rewrite
            simpa [hexp, hRnat] using h
          exact le_of_lt hrpow_lt
    exact le_trans hbound hmul_mk
  exact le_trans hscale hmain

theorem theorem5_exists_scaledMacro_radius (b : ℕ) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ b - 1 →
    ∃ k : ℕ,
      theorem5_T b k ≤ s ∧
        ((1 : ℝ) / 16) * Real.rpow s ((b : ℝ) / (b - 1)) ≤
          ((s - theorem5_T b k + 1) * dblMacroVal b k : ℝ) := by
  intro s hs
  classical
  obtain ⟨k, hkT, hklt⟩ := theorem5_exists_T_interval b hb s hs
  refine ⟨k, hkT, ?_⟩
  have hs_sub_nat : s - theorem5_T b k < (dblMacroVal b k) ^ (b - 1) := by
    have hklt' : s < (dblMacroVal b k) ^ (b - 1) + theorem5_T b k := by
      simpa [theorem5_T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hklt
    exact (Nat.sub_lt_iff_lt_add hkT).2 hklt'
  have hs_sub : (s - theorem5_T b k : ℝ) < (dblMacroVal b k : ℝ) ^ (b - 1) := by
    exact_mod_cast hs_sub_nat
  by_cases hsmall : (theorem5_T b k : ℝ) ≤ (s : ℝ) / 2
  · exact theorem5_exists_scaledMacro_radius_caseA b hb s k hkT hs_sub hsmall
  ·
    have hlarge : (s : ℝ) / 2 < (theorem5_T b k : ℝ) := lt_of_not_ge hsmall
    exact theorem5_exists_scaledMacro_radius_caseB b hb s k hkT hlarge

theorem theorem5_part2_upper_nat (b : ℕ) (hb : 2 ≤ b) :
  ∃ C₁ : ℝ,
    0 < C₁ ∧
      ∀ s : ℕ, s ≥ 1 →
        let rs := Real.rpow s ((b : ℝ) / (b - 1))
        ∀ n : ℕ, n ≤ Int.toNat (Int.ceil (C₁ * rs)) →
          theorem5_Rep b s n := by
  classical
  let C₁ : ℝ := (1 : ℝ) / (32 * (b : ℝ) ^ 2)
  have hC₁pos : (0 : ℝ) < C₁ := by
    have hden : (0 : ℝ) < 32 * (b : ℝ) ^ 2 := by positivity
    simpa [C₁, one_div] using (one_div_pos.mpr hden)
  refine ⟨C₁, hC₁pos, ?_⟩
  intro s hs
  dsimp
  set rs : ℝ := Real.rpow s ((b : ℝ) / (b - 1)) with hrs
  intro n hn
  have hn' : n ≤ ⌈C₁ * rs⌉₊ := by
    simpa [Nat.ceil] using hn
  by_cases hsb : s < b - 1
  · -- small s
    have hs_lt_b : s < b := lt_of_lt_of_le hsb (Nat.sub_le b 1)
    have hs_le_b : (s : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (le_of_lt hs_lt_b)
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hb)
    have hExp_nonneg : (0 : ℝ) ≤ (b : ℝ) / (b - 1) := by
      have hden_nonneg : (0 : ℝ) ≤ (b : ℝ) - 1 := sub_nonneg.mpr hb1
      exact div_nonneg (by positivity) hden_nonneg
    have hExp_le_two : (b : ℝ) / (b - 1) ≤ (2 : ℝ) := theorem5_exp_le_two b hb
    have hrs_le_bexp : rs ≤ Real.rpow b ((b : ℝ) / (b - 1)) := by
      have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by positivity
      simpa [rs] using (Real.rpow_le_rpow hs_nonneg hs_le_b hExp_nonneg)
    have hbexp_le_b2 : Real.rpow b ((b : ℝ) / (b - 1)) ≤ Real.rpow b (2 : ℝ) := by
      simpa using (Real.rpow_le_rpow_of_exponent_le hb1 hExp_le_two)
    have hrs_le_b2 : rs ≤ Real.rpow b (2 : ℝ) := le_trans hrs_le_bexp hbexp_le_b2
    have hb2_eq : Real.rpow b (2 : ℝ) = (b : ℝ) ^ 2 := by
      simp
    have hrs_le_b2' : rs ≤ (b : ℝ) ^ 2 := by
      simpa [hb2_eq] using hrs_le_b2
    have hCnonneg : (0 : ℝ) ≤ C₁ := le_of_lt hC₁pos
    have hCrs_le : C₁ * rs ≤ C₁ * (b : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hrs_le_b2' hCnonneg
    have hbne : (b : ℝ) ≠ 0 := by
      have hb0 : (0 : ℕ) < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
      exact_mod_cast (Nat.ne_of_gt hb0)
    have hCb2 : C₁ * (b : ℝ) ^ 2 = (1 : ℝ) / 32 := by
      unfold C₁
      field_simp [hbne]
    have hCrs_le32 : C₁ * rs ≤ (1 : ℝ) / 32 := by
      simpa [hCb2] using hCrs_le
    have hCrs_le1 : C₁ * rs ≤ (1 : ℝ) := by linarith
    have hceil1 : ⌈C₁ * rs⌉₊ ≤ 1 := (Nat.ceil_le).2 (by simpa using hCrs_le1)
    have hn1 : n ≤ 1 := le_trans hn' hceil1
    refine ⟨List.replicate n 1, ?_, ?_, ?_⟩
    · have : n ≤ s := le_trans hn1 hs
      simpa using this
    · intro t ht
      rcases (List.mem_replicate.1 ht) with ⟨_, rfl⟩
      left
      rfl
    · simp
  · -- large s
    have hsbig : s ≥ b - 1 := (not_lt).1 hsb
    rcases theorem5_exists_scaledMacro_radius b hb s hsbig with ⟨k, hkT, hkRad⟩
    have hrsnonneg : (0 : ℝ) ≤ rs := by
      have : (0 : ℝ) ≤ (s : ℝ) := by positivity
      exact Real.rpow_nonneg this _
    have hC1le : C₁ ≤ (1 : ℝ) / 16 := by
      -- since b ≥ 2, we have 16 ≤ 32*b^2
      have hb2 : (4 : ℝ) ≤ (b : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ (b : ℝ) := by
          exact_mod_cast hb
        nlinarith
      have hden_le : (16 : ℝ) ≤ 32 * (b : ℝ) ^ 2 := by
        nlinarith [hb2]
      have hpos : (0 : ℝ) < (16 : ℝ) := by norm_num
      have : (1 : ℝ) / (32 * (b : ℝ) ^ 2) ≤ (1 : ℝ) / 16 := by
        simpa [one_div] using (one_div_le_one_div_of_le hpos hden_le)
      simpa [C₁] using this
    have hCrs_le16 : C₁ * rs ≤ ((1 : ℝ) / 16) * rs := by
      have := mul_le_mul_of_nonneg_right hC1le hrsnonneg
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hCrs_leN : C₁ * rs ≤ (↑s - ↑(theorem5_T b k) + 1) * ↑(dblMacroVal b k) :=
      le_trans hCrs_le16 hkRad
    have hceil_leN : ⌈C₁ * rs⌉₊ ≤ (s - theorem5_T b k + 1) * dblMacroVal b k := by
      refine (Nat.ceil_le).2 ?_
      -- convert RHS to match the form from hkRad
      have : C₁ * rs ≤ (↑(s - theorem5_T b k) + 1) * ↑(dblMacroVal b k) := by
        -- rewrite `↑s - ↑T` as `↑(s - T)`
        simpa [Nat.cast_sub hkT, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hCrs_leN
      -- now package back as a coerced nat
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using this
    have hnN : n ≤ (s - theorem5_T b k + 1) * dblMacroVal b k := le_trans hn' hceil_leN
    exact theorem5_Rep_le_scaledMacro b hb k s n hkT hnN

theorem theorem5_part2_upper (b : ℕ) (hb : 2 ≤ b) :
  ∃ C₁ : ℝ,
    0 < C₁ ∧
      ∀ s : ℕ, s ≥ 1 →
        let rs := Real.rpow s ((b : ℝ) / (b - 1))
        Ball (Int.toNat (Int.ceil (C₁ * rs))) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) := by
  classical
  rcases theorem5_part2_upper_nat b hb with ⟨C₁, hC₁pos, hRep⟩
  refine ⟨C₁, hC₁pos, ?_⟩
  intro s hs
  dsimp
  intro m hm
  have hmcard : m.card ≤ Int.toNat (Int.ceil (C₁ * Real.rpow s ((b : ℝ) / (b - 1)))) :=
    (ball_A1_mem_iff_card_le (Int.toNat (Int.ceil (C₁ * Real.rpow s ((b : ℝ) / (b - 1))))) m).1 hm
  have hRep_s := hRep s hs
  dsimp at hRep_s
  rcases hRep_s m.card hmcard with ⟨l, hl, hcoins, hsum⟩
  exact (ball_macro_union_mem_iff_coinList b s m).2 ⟨l, hl, hcoins, hsum⟩

theorem theorem5_part2_expansion (b : ℕ) (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  ∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
      ∀ s : ℕ, s ≥ 1 →
        let rs := Real.rpow s ((b : ℝ) / (b - 1))
        (Ball (Int.toNat (Int.ceil (C₁ * rs))) (A 1) ⊆ Ball s (M ∪ A 1)) ∧
          ¬ (Ball (Int.toNat (Int.floor (C₂ * (s : ℝ) * rs))) (A 1) ⊆ Ball s (M ∪ A 1)) := by
  classical
  rcases theorem5_part2_upper b hb with ⟨C₁, hC₁pos, hC₁⟩
  rcases theorem5_part2_lower b hb with ⟨C₂, hC₂pos, hC₂⟩
  refine ⟨C₁, C₂, hC₁pos, hC₂pos, ?_⟩
  intro s hs
  dsimp
  constructor
  · simpa using hC₁ s hs
  · simpa using hC₂ s hs


theorem theorem5 (b : ℕ) (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  (∃ (d1 d2 : ℝ),
        ∀ (x : ℕ), x ≥ b ^ b →
          0 < d1 ∧
            0 < d2 ∧
              d1 * Real.log (Real.log x) ≤ (M ∩ Ball x (A 1)).ncard ∧
                (M ∩ Ball x (A 1)).ncard ≤ d2 * Real.log (Real.log x)) ∧
    (∃ C₁ C₂ : ℝ,
        0 < C₁ ∧
          0 < C₂ ∧
            ∀ (s : ℕ), s ≥ 1 →
              let rs := Real.rpow s ((b : ℝ) / (b - 1))
              (Ball (Int.toNat (Int.ceil (C₁ * rs))) (A 1) ⊆ Ball s (M ∪ A 1)) ∧
                ¬ (Ball (Int.toNat (Int.floor (C₂ * (s : ℝ) * rs))) (A 1) ⊆ Ball s (M ∪ A 1))) := by
  classical
  constructor
  · simpa using (theorem5_part1_density b hb)
  · simpa using (theorem5_part2_expansion b hb)
