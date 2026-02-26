import LeanFun.Definitions

open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, m = Multiset.replicate (b ^ (b ^ j)) i }

theorem theorem5_density (b : ℕ) (hb : 2 ≤ b) :
  ∃ (d1 d2 : ℝ), ∀ (x : ℕ), x ≥ b ^ b →
    0 < d1 ∧ 0 < d2 ∧
      d1 * (Real.log (Real.log x)) ≤ ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard ∧
      ((DoublyMacroSet b) ∩ Ball x (A 1)).ncard ≤ d2 * (Real.log (Real.log x)) := by
      sorry

theorem theorem5_lower_bound (b : ℕ) (hb : 2 ≤ b) :
  (∃ C₁ B : ℝ,
    0 < C₁ ∧
    (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆ Ball s (M ∪ (A 1))))
    ) := by
    sorry

theorem theorem5_upper_bound (b : ℕ) (hb : 2 ≤ b) :
  (∃ C₂ B : ℝ,
      0 < C₂ ∧
      (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆ Ball s (M ∪ (A 1)))
    ) := by
    sorry

theorem ball_mono_R_abelian {n : ℕ} {R R' : ℕ} {X : Set (abelian.FreeAbelianMonoid n)} : R ≤ R' → abelian.Ball (n := n) R X ⊆ abelian.Ball (n := n) R' X := by
  intro hRR'
  intro m hm
  rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩
  refine ⟨l, le_trans hl_len hRR', hl_mem, hl_sum⟩


theorem ball_mono_X_abelian {n : ℕ} {R : ℕ} {X Y : Set (abelian.FreeAbelianMonoid n)} : X ⊆ Y → abelian.Ball (n := n) R X ⊆ abelian.Ball (n := n) R Y := by
  intro hXY
  intro x hx
  classical
  simp [abelian.Ball] at hx ⊢
  rcases hx with ⟨l, hlR, hlX, rfl⟩
  refine ⟨l, hlR, ?_, rfl⟩
  intro z hz
  exact hXY (hlX z hz)


def buildBlocks_fin1 (b : ℕ) : List ℕ → ℕ → List (FreeAbelianMonoid 1) :=
  fun ds =>
    ds.recOn (fun _ => [])
      (fun d ds ih j =>
        List.replicate d (Multiset.replicate (b ^ j) (0 : Fin 1)) ++ ih (j + 1))

theorem buildBlocks_fin1_length (b : ℕ) :
  ∀ (ds : List ℕ) (j : ℕ), (buildBlocks_fin1 b ds j).length = ds.sum := by
  intro ds j
  induction ds generalizing j with
  | nil =>
      simp [buildBlocks_fin1]
  | cons d ds ih =>
      -- j is already in context
      -- unfold once and compute length
      have htail : (List.rec (motive := fun x => ℕ → List (FreeAbelianMonoid 1)) (fun _ => [])
          (fun d ds ih j =>
            List.replicate d (Multiset.replicate (b ^ j) (0 : Fin 1)) ++ ih (j + 1)) ds (j + 1)).length =
          ds.sum := by
        simpa [buildBlocks_fin1] using ih (j + 1)
      -- now finish by simp
      simpa [buildBlocks_fin1, List.sum_cons, List.length_append, List.length_replicate, htail, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]

theorem buildBlocks_fin1_mem_macro_union (b : ℕ) :
  ∀ (ds : List ℕ) (j : ℕ) (m : FreeAbelianMonoid 1),
    m ∈ buildBlocks_fin1 b ds j → m ∈ (MacroSet 1 b ∪ A 1) := by
  intro ds
  induction ds with
  | nil =>
      intro j m hm
      simp [buildBlocks_fin1] at hm
  | cons d ds ih =>
      intro j m hm
      simp [buildBlocks_fin1] at hm
      rcases hm with hrep | htail
      · rcases hrep with ⟨hd, rfl⟩
        cases j with
        | zero =>
            right
            refine ⟨(0 : Fin 1), ?_⟩
            simpa [Multiset.replicate_one]
        | succ j' =>
            left
            refine ⟨(0 : Fin 1), j'.succ, ?_, rfl⟩
            simp
      · exact ih (j + 1) m htail
  

theorem buildBlocks_fin1_sum (b : ℕ) :
  ∀ (ds : List ℕ) (j : ℕ),
    (buildBlocks_fin1 b ds j).sum =
      Multiset.replicate (Nat.ofDigits b ds * b ^ j) (0 : Fin 1) := by
  intro ds j
  induction ds generalizing j with
  | nil =>
      simp [buildBlocks_fin1, Nat.ofDigits_nil]
  | cons d ds ih =>
      -- reduce the goal to the tail case
      simp [buildBlocks_fin1, List.sum_append, List.sum_replicate, Multiset.nsmul_replicate,
        Nat.ofDigits_cons, pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Multiset.replicate_add]
      -- finish using the induction hypothesis
      simpa [buildBlocks_fin1, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ih (j + 1)

theorem digits_sum_le_mul_of_lt_pow (b : ℕ) (k : ℕ) (x : ℕ) (hb : 2 ≤ b) (hx : x < b ^ k) :
  (Nat.digits b x).sum ≤ k * (b - 1) := by
  have hb1 : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
  have hlen : (Nat.digits b x).length ≤ k := by
    exact (Nat.digits_length_le_iff hb1 x).2 hx
  have hsum : (Nat.digits b x).sum ≤ (Nat.digits b x).length * (b - 1) := by
    simpa [Nat.nsmul_eq_mul] using
      (List.sum_le_card_nsmul (l := Nat.digits b x) (n := (b - 1)) (by
        intro d hd
        have hdlt : d < b := Nat.digits_lt_base hb1 hd
        exact Order.le_sub_one_of_lt hdlt))
  exact le_trans hsum (Nat.mul_le_mul_right (b - 1) hlen)

theorem eventually_const_mul_sq_lt_pow (b : ℕ) (hb : 2 ≤ b) (C : ℝ) (hC : 0 < C) :
  ∃ N : ℕ, ∀ n ≥ N, C * (n : ℝ) ^ (2 : ℕ) < (b : ℝ) ^ n := by
  classical
  have hb1_nat : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb1_nat
  have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 : ℕ) / (b : ℝ) ^ n) Filter.atTop
      (nhds (0 : ℝ)) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt (k := 2) (r := (b : ℝ)) hb1)
  have hε : 0 < (1 / C) := by
    exact one_div_pos.2 hC
  rcases (NormedAddCommGroup.tendsto_atTop.1 hlim) (1 / C) hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hnorm : ‖(fun n : ℕ => (n : ℝ) ^ (2 : ℕ) / (b : ℝ) ^ n) n - (0 : ℝ)‖ < 1 / C := by
    exact hN n hn
  have hnorm' : ‖(n : ℝ) ^ (2 : ℕ) / (b : ℝ) ^ n‖ < 1 / C := by
    simpa [sub_zero] using hnorm
  have hbpos_nat : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  have hbpos : 0 < (b : ℝ) := by
    exact_mod_cast hbpos_nat
  have hpowpos : 0 < (b : ℝ) ^ n := by
    exact pow_pos hbpos n
  have hx_nonneg : 0 ≤ (n : ℝ) ^ (2 : ℕ) / (b : ℝ) ^ n := by
    exact div_nonneg (by positivity) (le_of_lt hpowpos)
  have hx_lt : (n : ℝ) ^ (2 : ℕ) / (b : ℝ) ^ n < 1 / C := by
    simpa [Real.norm_of_nonneg hx_nonneg] using hnorm'
  have hmain : (n : ℝ) ^ (2 : ℕ) < (1 / C) * (b : ℝ) ^ n := by
    exact (div_lt_iff₀ hpowpos).1 hx_lt
  have hmain' : C * ((n : ℝ) ^ (2 : ℕ)) < C * ((1 / C) * (b : ℝ) ^ n) := by
    exact (mul_lt_mul_of_pos_left hmain hC)
  have hCne : C ≠ 0 := ne_of_gt hC
  -- simplify and conclude
  simpa [mul_assoc, mul_left_comm, mul_comm, one_div, hCne] using hmain'

theorem replicate_mem_ball_macro_union_digits_fin1 (b : ℕ) :
  ∀ x : ℕ,
    Multiset.replicate x (0 : Fin 1) ∈
      Ball ((Nat.digits b x).sum) ((MacroSet 1 b) ∪ (A 1)) := by
  intro x
  let ds : List ℕ := Nat.digits b x
  let l : List (FreeAbelianMonoid 1) := buildBlocks_fin1 b ds 0
  refine ⟨l, ?_, ?_, ?_⟩
  ·
    have hlen : l.length = ds.sum := by
      simpa [l] using buildBlocks_fin1_length b ds 0
    have hlen' : l.length ≤ ds.sum := le_of_eq hlen
    simpa [ds] using hlen'
  ·
    intro m hm
    have hm' : m ∈ buildBlocks_fin1 b ds 0 := by
      simpa [l] using hm
    exact buildBlocks_fin1_mem_macro_union b ds 0 m hm'
  ·
    have hsum : l.sum = Multiset.replicate (Nat.ofDigits b ds * b ^ 0) (0 : Fin 1) := by
      simpa [l] using buildBlocks_fin1_sum b ds 0
    have hdigits : Nat.ofDigits b ds = x := by
      simpa [ds] using (Nat.ofDigits_digits b x)
    -- finish by rewriting
    calc
      l.sum = Multiset.replicate (Nat.ofDigits b ds * b ^ 0) (0 : Fin 1) := hsum
      _ = Multiset.replicate (Nat.ofDigits b ds) (0 : Fin 1) := by
        simp only [pow_zero, Nat.mul_one]
      _ = Multiset.replicate x (0 : Fin 1) := by
        simpa [hdigits]


theorem replicate_pow_mem_ball_macro_union_fin1 (b : ℕ) (hb : 2 ≤ b) (k : ℕ) (hk : 1 ≤ k) :
  Multiset.replicate (b ^ k) (0 : Fin 1) ∈
    Ball ((b - 1) * k) ((MacroSet 1 b) ∪ (A 1)) := by
  -- try to follow informal proof
  have hm_macro : Multiset.replicate (b ^ k) (0 : Fin 1) ∈ MacroSet 1 b := by
    refine ⟨(0 : Fin 1), k, hk, rfl⟩
  have hm_ball1 : Multiset.replicate (b ^ k) (0 : Fin 1) ∈ Ball (n := 1) 1 ((MacroSet 1 b) ∪ (A 1)) := by
    -- unfold Ball
    refine ⟨[Multiset.replicate (b ^ k) (0 : Fin 1)], ?_⟩
    refine ⟨by simp, ?_⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx' : x = Multiset.replicate (b ^ k) (0 : Fin 1) := by
        simpa using hx
      subst hx'
      exact Or.inl hm_macro
    · simp
  have hR : (1 : ℕ) ≤ (b - 1) * k := by
    have hb1 : (1 : ℕ) ≤ b - 1 := by
      have := Nat.sub_le_sub_right hb 1
      simpa using this
    have h := Nat.mul_le_mul hb1 hk
    simpa using h
  -- use monotonicity of Ball
  exact (ball_mono_R_abelian (n := 1) (R := 1) (R' := (b - 1) * k) (X := (MacroSet 1 b ∪ A 1)) hR) hm_ball1

theorem rpow_le_pow_two_of_b_ge_2 (b : ℕ) (hb : 2 ≤ b) :
  ∀ {s : ℝ}, 1 ≤ s →
    Real.rpow s ((b : ℝ) / (b - 1)) ≤ s ^ (2 : ℝ) := by
  intro s hs
  have hb1 : (1 : ℕ) ≤ b := by
    exact le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    simpa using (Nat.cast_sub hb1)
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hb
  have hpos : (0 : ℝ) < (b : ℝ) - 1 := by
    linarith [hbR]
  have hmul : (b : ℝ) ≤ (2 : ℝ) * ((b : ℝ) - 1) := by
    linarith [hbR]
  have hexp' : (b : ℝ) / ((b : ℝ) - 1) ≤ (2 : ℝ) := by
    exact (div_le_iff₀ hpos).2 hmul
  have hexp : (b : ℝ) / (b - 1) ≤ (2 : ℝ) := by
    simpa [hcast] using hexp'
  have hrpow : Real.rpow s ((b : ℝ) / (b - 1)) ≤ Real.rpow s (2 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hs hexp
  simpa using hrpow

theorem sum_A1_list_eq_replicate_length_fin1 (l : List (FreeAbelianMonoid 1)) :
  (∀ x, x ∈ l → x ∈ A 1) →
    l.sum = Multiset.replicate l.length (0 : Fin 1) := by
  intro hl
  revert hl
  induction l with
  | nil =>
      intro hl
      simp
  | cons a t ih =>
      intro hl
      have ha : a ∈ A 1 := hl a (by simp)
      rcases ha with ⟨i, rfl⟩
      have hi0 : i = (0 : Fin 1) := Subsingleton.elim i 0
      subst hi0
      have ht : ∀ x, x ∈ t → x ∈ A 1 := by
        intro x hx
        exact hl x (by simp [hx])
      have htSum : t.sum = Multiset.replicate t.length (0 : Fin 1) := ih ht
      have hadd :
          ({0} : Multiset (Fin 1)) + Multiset.replicate t.length (0 : Fin 1) =
            Multiset.replicate (t.length + 1) (0 : Fin 1) := by
        calc
          ({0} : Multiset (Fin 1)) + Multiset.replicate t.length (0 : Fin 1) =
              Multiset.replicate 1 (0 : Fin 1) + Multiset.replicate t.length (0 : Fin 1) := by
            simpa [Multiset.replicate_one]
          _ = Multiset.replicate (1 + t.length) (0 : Fin 1) := by
            simpa using (Multiset.replicate_add 1 t.length (0 : Fin 1)).symm
          _ = Multiset.replicate (t.length + 1) (0 : Fin 1) := by
            simpa [Nat.add_comm]
      simpa [List.sum_cons, htSum, List.length_cons, hadd]


theorem ball_pow_subset_ball_macro_union_one (b : ℕ) (hb : 2 ≤ b) :
  ∀ k : ℕ, 1 ≤ k →
    Ball (b ^ k) (A 1) ⊆ Ball ((b - 1) * k) ((MacroSet 1 b) ∪ (A 1)) := by
  intro k hk
  intro m hm
  rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩
  set x : ℕ := l.length with hx
  have hxle : x ≤ b ^ k := by
    simpa [hx] using hl_len
  have hsumrep : l.sum = Multiset.replicate x (0 : Fin 1) := by
    simpa [hx] using (sum_A1_list_eq_replicate_length_fin1 l hl_mem)
  have hm_eq : m = l.sum := by
    simpa [eq_comm] using hl_sum
  have hmrep : m = Multiset.replicate x (0 : Fin 1) := by
    exact hm_eq.trans hsumrep
  have hxlt_or_eq : x < b ^ k ∨ x = b ^ k := lt_or_eq_of_le hxle
  cases hxlt_or_eq with
  | inl hxlt =>
      have hxmem : Multiset.replicate x (0 : Fin 1) ∈
          Ball ((Nat.digits b x).sum) ((MacroSet 1 b) ∪ (A 1)) := by
        simpa using (replicate_mem_ball_macro_union_digits_fin1 (b := b) x)
      have hrad : (Nat.digits b x).sum ≤ (b - 1) * k := by
        simpa [Nat.mul_comm] using (digits_sum_le_mul_of_lt_pow b k x hb hxlt)
      have hxmem' : Multiset.replicate x (0 : Fin 1) ∈
          Ball ((b - 1) * k) ((MacroSet 1 b) ∪ (A 1)) := by
        exact (ball_mono_R_abelian (n := 1) (R := (Nat.digits b x).sum) (R' := (b - 1) * k)
          (X := (MacroSet 1 b ∪ A 1)) hrad) hxmem
      simpa [hmrep] using hxmem'
  | inr hxeq =>
      have hxmem : Multiset.replicate (b ^ k) (0 : Fin 1) ∈
          Ball ((b - 1) * k) ((MacroSet 1 b) ∪ (A 1)) := by
        simpa using (replicate_pow_mem_ball_macro_union_fin1 (b := b) hb k hk)
      have hxmemx : Multiset.replicate x (0 : Fin 1) ∈
          Ball ((b - 1) * k) ((MacroSet 1 b) ∪ (A 1)) := by
        simpa [hxeq] using hxmem
      simpa [hmrep] using hxmemx

theorem theorem5_upper_bound_neg_from_reform (b : ℕ) (hb : 2 ≤ b) :
  (∀ (C₂ B : ℝ), 0 < C₂ →
    ∃ s : ℕ, (s : ℝ) ≥ B ∧
      (let rs := Real.rpow s ((b : ℝ) / (b - 1));
        Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆
          Ball s ((MacroSet 1 b) ∪ (A 1))))
  →
  ¬ (∃ C₂ B : ℝ,
      0 < C₂ ∧
      (∀ (s : ℕ), (s : ℝ) ≥ B →
        let rs := Real.rpow s ((b : ℝ) / (b - 1));
        ¬ (Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆
            Ball s ((MacroSet 1 b) ∪ (A 1))))
    ) := by
  intro hReform hExists
  rcases hExists with ⟨C₂, B, hC₂pos, hforall⟩
  rcases hReform C₂ B hC₂pos with ⟨s, hsB, hsIncl⟩
  have hbad := hforall s hsB
  exact hbad (by
    simpa using hsIncl)


theorem theorem5_upper_bound_neg_iff_reform (b : ℕ) (hb : 2 ≤ b) :
  (¬ (∃ C₂ B : ℝ,
        0 < C₂ ∧
        (∀ (s : ℕ), (s : ℝ) ≥ B →
          let rs := Real.rpow s ((b : ℝ) / (b - 1));
          ¬ (Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆
              Ball s ((MacroSet 1 b) ∪ (A 1)))))
    )
    ↔
    (∀ (C₂ B : ℝ), 0 < C₂ →
      ∃ s : ℕ, (s : ℝ) ≥ B ∧
        (let rs := Real.rpow s ((b : ℝ) / (b - 1));
          Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆
            Ball s ((MacroSet 1 b) ∪ (A 1)))) := by
  classical
  constructor
  · intro hnot
    intro C₂ B hC₂
    by_contra hno
    apply hnot
    refine ⟨C₂, B, hC₂, ?_⟩
    intro s hsB
    dsimp
    intro hsIncl
    apply hno
    refine ⟨s, hsB, ?_⟩
    simpa using hsIncl
  · intro hReform
    intro hExists
    rcases hExists with ⟨C₂, B, hC₂, hforall⟩
    rcases hReform C₂ B hC₂ with ⟨s, hsB, hsIncl⟩
    have hbad := hforall s hsB
    exact hbad (by
      simpa using hsIncl)


theorem theorem5_upper_bound_neg_reform (b : ℕ) (hb : 2 ≤ b) :
  ∀ (C₂ B : ℝ), 0 < C₂ →
    ∃ s : ℕ, (s : ℝ) ≥ B ∧
      (let rs := Real.rpow s ((b : ℝ) / (b - 1));
        Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆
          Ball s ((MacroSet 1 b) ∪ (A 1))) := by
  intro C₂ B hC₂
  classical
  have hb1 : 1 ≤ b - 1 := by omega
  have hb1pos : 0 < ((b - 1 : ℕ) : ℝ) := by
    have hb1' : (1 : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by
      exact_mod_cast hb1
    have : (0 : ℝ) < (1 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hb1'
  have hC : 0 < C₂ * ((b - 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
    have : 0 < ((b - 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
      exact pow_pos hb1pos _
    exact mul_pos hC₂ this
  rcases eventually_const_mul_sq_lt_pow b hb (C₂ * ((b - 1 : ℕ) : ℝ) ^ (2 : ℕ)) hC with ⟨N, hN⟩
  let k : ℕ := max 1 (max (Nat.ceil B) N)
  have hk1 : 1 ≤ k := by
    dsimp [k]
    exact le_max_left _ _
  have hkN : N ≤ k := by
    dsimp [k]
    exact le_trans (le_max_right (Nat.ceil B) N) (le_max_right 1 (max (Nat.ceil B) N))
  have hkceil : Nat.ceil B ≤ k := by
    dsimp [k]
    exact le_trans (le_max_left (Nat.ceil B) N) (le_max_right 1 (max (Nat.ceil B) N))
  have hkB : (k : ℝ) ≥ B := by
    have hBceil : (B : ℝ) ≤ (Nat.ceil B : ℝ) := by
      simpa using (Nat.le_ceil B)
    have hceilk : (Nat.ceil B : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hkceil
    exact le_trans hBceil hceilk
  let s : ℕ := (b - 1) * k
  have hs_ge_k : k ≤ s := by
    dsimp [s]
    simpa [Nat.mul_comm] using (Nat.mul_le_mul_right k hb1)
  have hsB : (s : ℝ) ≥ B := by
    have hk_le_hs : (k : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs_ge_k
    exact le_trans hkB hk_le_hs
  refine ⟨s, hsB, ?_⟩
  dsimp
  set rs : ℝ := Real.rpow (s : ℝ) ((b : ℝ) / (b - 1))
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
    have : (1 : ℕ) ≤ s := by
      dsimp [s]
      exact Nat.mul_le_mul hb1 hk1
    exact_mod_cast this
  have hrs_le : rs ≤ (s : ℝ) ^ (2 : ℝ) := by
    simpa [rs] using (rpow_le_pow_two_of_b_ge_2 b hb (s := (s : ℝ)) hs1)
  have hrs_le_sq : rs ≤ (s : ℝ) ^ (2 : ℕ) := by
    simpa [Real.rpow_two] using hrs_le
  have hk_big : C₂ * (s : ℝ) ^ (2 : ℕ) < (b : ℝ) ^ k := by
    have hkineq := hN k hkN
    -- Rewrite the LHS of hkineq to match `C₂ * (s:ℝ)^2`.
    -- `simp` uses: `s = (b-1)*k`, `Nat.cast_mul`, `mul_pow`.
    simpa [s, Nat.cast_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hkineq
  have hCrs_lt : C₂ * rs < (b : ℝ) ^ k := by
    have hle : C₂ * rs ≤ C₂ * (s : ℝ) ^ (2 : ℕ) := by
      have := mul_le_mul_of_nonneg_left hrs_le_sq (le_of_lt hC₂)
      simpa [mul_assoc] using this
    exact lt_of_le_of_lt hle hk_big
  have hfloor_lt : Nat.floor (C₂ * rs) < b ^ k := by
    have hn : b ^ k ≠ 0 := by
      have hb0 : b ≠ 0 := by
        have : (0 : ℕ) < b := by omega
        exact ne_of_gt this
      exact pow_ne_zero _ hb0
    have : Nat.floor (C₂ * rs) < b ^ k ↔ (C₂ * rs) < (b ^ k : ℝ) := by
      simpa using (Nat.floor_lt' (a := C₂ * rs) (n := b ^ k) hn)
    exact (this.mpr (by simpa using hCrs_lt))
  have hR_le : 1 + Int.toNat (Int.floor (C₂ * rs)) ≤ b ^ k := by
    have hfloor_lt' : Int.toNat (Int.floor (C₂ * rs)) < b ^ k := by
      simpa [Int.floor_toNat] using hfloor_lt
    have : Int.toNat (Int.floor (C₂ * rs)) + 1 ≤ b ^ k := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_le_iff.2 hfloor_lt')
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have hBall_mono : Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆ Ball (b ^ k) (A 1) := by
    exact ball_mono_R_abelian (n := 1) hR_le
  have hBall_pow : Ball (b ^ k) (A 1) ⊆ Ball s ((MacroSet 1 b) ∪ (A 1)) := by
    simpa [s] using (ball_pow_subset_ball_macro_union_one b hb k hk1)
  exact Set.Subset.trans hBall_mono hBall_pow

theorem theorem5_upper_bound_neg (b : ℕ) (hb : 2 ≤ b) :
  ¬ (∃ C₂ B : ℝ,
      0 < C₂ ∧
      (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆
          Ball s ((MacroSet 1 b) ∪ (A 1)))
    ) := by
  have hiff := theorem5_upper_bound_neg_iff_reform (b := b) (hb := hb)
  exact hiff.2 (theorem5_upper_bound_neg_reform (b := b) (hb := hb))


theorem theorem5
  (b : ℕ)
  (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b ^ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ (Ball x (A 1))).ncard
      ∧ (M ∩ (Ball x (A 1))).ncard ≤ d2 * (Real.log (Real.log x))) ∧
  (∃ C₁ C₂ B : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
        ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆ Ball s (M ∪ (A 1)))
    ) :=
  sorry
