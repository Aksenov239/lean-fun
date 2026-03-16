import LeanFun.Definitions

open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, m = Multiset.replicate (b ^ (b ^ j)) i }

theorem Ball_add_A1 {R S : ℕ} {X : Set (FreeAbelianMonoid 1)} {m₁ m₂ : FreeAbelianMonoid 1} : m₁ ∈ Ball R X → m₂ ∈ Ball S X → m₁ + m₂ ∈ Ball (R + S) X := by
  intro hm₁ hm₂
  rcases hm₁ with ⟨l₁, hlen₁, hmem₁, hsum₁⟩
  rcases hm₂ with ⟨l₂, hlen₂, hmem₂, hsum₂⟩
  refine ⟨l₁ ++ l₂, ?_, ?_, ?_⟩
  · simpa [List.length_append] using Nat.add_le_add hlen₁ hlen₂
  · intro x hx
    rw [List.mem_append] at hx
    cases hx with
    | inl hx₁ => exact hmem₁ x hx₁
    | inr hx₂ => exact hmem₂ x hx₂
  · simpa [hsum₁, hsum₂] using List.sum_append l₁ l₂

theorem Ball_mono_R_A1 (R R' : ℕ) {X : Set (FreeAbelianMonoid 1)} : R ≤ R' → Ball R X ⊆ Ball R' X := by
  intro hRR' x hx
  rcases hx with ⟨l, hlR, hlX, rfl⟩
  exact ⟨l, le_trans hlR hRR', hlX, rfl⟩

def doubleMacroNat (b k : ℕ) : ℕ := b ^ (b ^ k)

theorem doubleMacroNat_succ (b k : ℕ) : doubleMacroNat b (k + 1) = (doubleMacroNat b k) ^ b := by
  unfold doubleMacroNat
  rw [Nat.pow_succ, pow_mul]

theorem doubleMacroNat_mono (b i j : ℕ) (hb : 2 ≤ b) : i ≤ j → doubleMacroNat b i ≤ doubleMacroNat b j := by
  intro hij
  induction hij with
  | refl =>
      exact le_rfl
  | @step j hij ih =>
      rw [doubleMacroNat_succ]
      exact le_trans ih (Nat.le_pow (a := doubleMacroNat b j) (by omega))

def doubleMacroPrefix (b K : ℕ) : Finset (FreeAbelianMonoid 1) :=
  (Finset.range (K + 1)).image (fun j => Multiset.replicate (doubleMacroNat b j) (0 : Fin 1))

theorem doubleMacro_index_lt_pow (b n : ℕ) (hb : 2 ≤ b) : n < (doubleMacroNat b n) ^ (b - 1) := by
  have h1 : n < 2 ^ n := by
    exact Nat.lt_two_pow_self
  have hb1 : 2 ^ n ≤ b ^ n := by
    exact Nat.pow_le_pow_left hb n
  have hnle : n ≤ b ^ n := by
    exact le_trans (Nat.le_of_lt h1) hb1
  have h2 : b ^ n ≤ b ^ (b ^ n) := by
    exact Nat.pow_le_pow_of_le hb hnle
  have h3 : doubleMacroNat b n ≤ (doubleMacroNat b n) ^ (b - 1) := by
    exact Nat.le_self_pow (by omega) (doubleMacroNat b n)
  exact lt_of_lt_of_le (lt_of_lt_of_le h1 (le_trans hb1 h2)) h3

theorem doubleMacro_find_scale_lower (b s : ℕ) (hb : 2 ≤ b) (hs : 2 * (doubleMacroNat b 0) ^ (b - 1) ≤ s) : let R : ℕ → ℕ := fun k => 2 * (doubleMacroNat b k) ^ (b - 1); let k := Nat.findGreatest (fun j => R j ≤ s) s; R k ≤ s ∧ s < R (k + 1) := by
  dsimp
  let R : ℕ → ℕ := fun k => 2 * (doubleMacroNat b k) ^ (b - 1)
  let k := Nat.findGreatest (fun j => R j ≤ s) s
  have h0 : R 0 ≤ s := by
    simpa [R] using hs
  have hk_le : R k ≤ s := by
    exact Nat.findGreatest_spec (P := fun j => R j ≤ s) (m := 0) (n := s) (Nat.zero_le s) h0
  constructor
  · exact hk_le
  · change s < R (k + 1)
    by_cases hks : k = s
    · rw [hks]
      let t := (doubleMacroNat b (s + 1)) ^ (b - 1)
      have hlt1 : s + 1 < t := by
        simpa [t] using doubleMacro_index_lt_pow b (s + 1) hb
      have hlt : s < t := by
        exact lt_trans (Nat.lt_succ_self s) hlt1
      have hmul : t ≤ 2 * t := by
        simpa [two_mul] using (Nat.le_add_right t t)
      simpa [R, t] using lt_of_lt_of_le hlt hmul
    · have hk_bound : k ≤ s := by
        simpa [k] using (Nat.findGreatest_le (P := fun j => R j ≤ s) s)
      have hks' : k < s := by
        exact lt_of_le_of_ne hk_bound hks
      have hk1 : k + 1 ≤ s := Nat.succ_le_of_lt hks'
      have hk_lt_succ : Nat.findGreatest (fun j => R j ≤ s) s < k + 1 := by
        simpa [k] using (Nat.lt_succ_self k)
      have hnot : ¬ R (k + 1) ≤ s := by
        exact Nat.findGreatest_is_greatest (P := fun j => R j ≤ s) (n := s) (k := k + 1) hk_lt_succ hk1
      exact Nat.lt_of_not_ge hnot

theorem doubleMacro_find_scale_upper (b s : ℕ) (hb : 2 ≤ b) (hs : (doubleMacroNat b 0) ^ (b - 1) ≤ s) : let k := Nat.findGreatest (fun j => (doubleMacroNat b j) ^ (b - 1) ≤ s) s; (doubleMacroNat b k) ^ (b - 1) ≤ s ∧ s < (doubleMacroNat b (k + 1)) ^ (b - 1) := by
  dsimp
  let P : ℕ → Prop := fun j => (doubleMacroNat b j) ^ (b - 1) ≤ s
  set k : ℕ := Nat.findGreatest P s
  refine ⟨?_, ?_⟩
  · have hk_spec : P (Nat.findGreatest P s) := Nat.findGreatest_spec (m := 0) (n := s) (by omega) hs
    simpa [P, k] using hk_spec
  · by_cases hks : k = s
    · have hslt : s < (doubleMacroNat b (s + 1)) ^ (b - 1) := by
          exact lt_trans (Nat.lt_succ_self s) (doubleMacro_index_lt_pow b (s + 1) hb)
      simpa [hks] using hslt
    · have hk_le : k ≤ s := by
          simpa [k] using (Nat.findGreatest_le (P := P) s)
      have hlt : k < s := Nat.lt_of_le_of_ne hk_le hks
      have hk1_le : k + 1 ≤ s := Nat.succ_le_of_lt hlt
      have hk1_not : ¬ P (k + 1) := by
        have hfg_lt : Nat.findGreatest P s < k + 1 := by
          simpa [k]
        exact Nat.findGreatest_is_greatest (P := P) (n := s) (k := k + 1) hfg_lt hk1_le
      exact Nat.lt_of_not_ge (by simpa [P] using hk1_not)

theorem doubleMacro_log_lower_bound (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) : ((((Nat.log b (Nat.log b x) : ℕ) : ℝ) - 1) * Real.log b ≤ Real.log (Real.log x)) := by
  let m := Nat.log b x
  let k := Nat.log b m
  have hb1 : 1 < b := by omega
  have hb0 : 0 < b := by omega
  have hbR_pos : 0 < (b : ℝ) := by
    exact_mod_cast hb0
  have hlogb_pos : 0 < Real.log b := by
    have hbR1 : (1 : ℝ) < b := by
      exact_mod_cast hb1
    exact Real.log_pos hbR1
  have hm_ge_b : b ≤ m := by
    simpa [m] using Nat.le_log_of_pow_le hb1 hx
  have hm_ge_two : 2 ≤ m := by
    omega
  have hm_pos : 0 < m := by
    omega
  have hm_ne_zero : m ≠ 0 := by
    omega
  have hmR_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm_pos
  have hx_pos : 0 < x := by
    have hpow_pos : 0 < b ^ b := Nat.pow_pos hb0
    exact lt_of_lt_of_le hpow_pos hx
  have hxR_pos : 0 < (x : ℝ) := by
    exact_mod_cast hx_pos
  have hk_ge_one : 1 ≤ k := by
    apply Nat.le_log_of_pow_le hb1
    simpa [k] using hm_ge_b
  have hpow_k : (b : ℝ) ^ k ≤ m := by
    exact_mod_cast (Nat.pow_log_le_self b hm_ne_zero)
  have hkm : (k : ℝ) * Real.log b ≤ Real.log m := by
    exact (Real.pow_le_iff_le_log hbR_pos hmR_pos).1 hpow_k
  have hpow_m : (b : ℝ) ^ m ≤ x := by
    exact_mod_cast (Nat.pow_log_le_self b (by omega : x ≠ 0))
  have hmx : (m : ℝ) * Real.log b ≤ Real.log x := by
    exact (Real.pow_le_iff_le_log hbR_pos hxR_pos).1 hpow_m
  have hmul_pos : 0 < (m : ℝ) * Real.log b := by
    exact mul_pos hmR_pos hlogb_pos
  have hlogx_pos : 0 < Real.log x := by
    exact lt_of_lt_of_le hmul_pos hmx
  have hstep : Real.log m + Real.log (Real.log b) ≤ Real.log (Real.log x) := by
    have h : Real.log ((m : ℝ) * Real.log b) ≤ Real.log (Real.log x) := by
      exact Real.log_le_log hmul_pos hmx
    rw [Real.log_mul hmR_pos.ne' hlogb_pos.ne'] at h
    exact h
  have hmain : (k : ℝ) * Real.log b + Real.log (Real.log b) ≤ Real.log (Real.log x) := by
    linarith
  have h_inv_le : (b : ℝ)⁻¹ ≤ Real.log b := by
    have h1 : 1 - (b : ℝ)⁻¹ ≤ Real.log b := by
      exact Real.one_sub_inv_le_log_of_pos hbR_pos
    have h2 : (b : ℝ)⁻¹ ≤ 1 - (b : ℝ)⁻¹ := by
      have haux : (2 : ℝ) * (b : ℝ)⁻¹ ≤ (b : ℝ) * (b : ℝ)⁻¹ := by
        gcongr
        exact_mod_cast hb
      have h2mul : (2 : ℝ) * (b : ℝ)⁻¹ ≤ 1 := by
        simpa [hbR_pos.ne'] using haux
      linarith
    exact le_trans h2 h1
  have hneglog_le : -Real.log b ≤ Real.log (Real.log b) := by
    have hb_inv_pos : 0 < (b : ℝ)⁻¹ := by
      positivity
    have h : Real.log ((b : ℝ)⁻¹) ≤ Real.log (Real.log b) := by
      exact Real.log_le_log hb_inv_pos h_inv_le
    simpa using h
  have hfinal : ((k : ℝ) - 1) * Real.log b ≤ Real.log (Real.log x) := by
    linarith
  simpa [m, k] using hfinal

theorem doubleMacro_log_upper_bound (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) : Real.log (Real.log x) < ((((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 2) * Real.log b) := by
  let m := Nat.log b x
  let k := Nat.log b m
  have hb1 : 1 < b := by
    omega
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb1
  have hbR0 : (0 : ℝ) < b := by
    exact_mod_cast hb0
  have hbR1 : (1 : ℝ) < b := by
    exact_mod_cast hb1
  have hx0 : 0 < x := by
    refine lt_of_lt_of_le ?_ hx
    exact Nat.pow_pos hb0
  have hxR0 : (0 : ℝ) < x := by
    exact_mod_cast hx0
  have hbx : b < x := by
    exact lt_of_lt_of_le (Nat.lt_pow_self hb1) hx
  have hxR1 : (1 : ℝ) < x := by
    exact lt_trans hbR1 (by exact_mod_cast hbx)
  have hxRnonneg : (0 : ℝ) ≤ x := by
    exact_mod_cast (Nat.zero_le x)
  have hlogb_pos : 0 < Real.log b := by
    rw [Real.log_pos_iff (show (0 : ℝ) ≤ b by exact le_of_lt hbR0)]
    exact hbR1
  have hlogb_lt_b : Real.log b < b := by
    have h := Real.log_lt_sub_one_of_pos hbR0 (by exact_mod_cast (Nat.ne_of_gt hb1))
    linarith
  have hxm : x < b ^ (m + 1) := by
    simpa [m, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hb1 x
  have hlogx_lt' : Real.log x < Real.log ((b : ℝ) ^ (m + 1)) := by
    exact Real.log_lt_log hxR0 (by exact_mod_cast hxm)
  have hlogx_lt : Real.log x < (((m : ℕ) : ℝ) + 1) * Real.log b := by
    simpa [Nat.cast_add, Nat.cast_one, m] using hlogx_lt'
  have hlogx_pos : 0 < Real.log x := by
    rw [Real.log_pos_iff hxRnonneg]
    exact hxR1
  have hm1R0 : (0 : ℝ) < ((m : ℕ) : ℝ) + 1 := by
    positivity
  have hloglogx_lt : Real.log (Real.log x) < Real.log ((((m : ℕ) : ℝ) + 1) * Real.log b) := by
    exact Real.log_lt_log hlogx_pos hlogx_lt
  have hloglogx_lt' : Real.log (Real.log x) < Real.log (((m : ℕ) : ℝ) + 1) + Real.log (Real.log b) := by
    rw [Real.log_mul hm1R0.ne' hlogb_pos.ne'] at hloglogx_lt
    simpa using hloglogx_lt
  have hbm : b ≤ m := by
    simpa [m] using Nat.le_log_of_pow_le hb1 hx
  have hm0 : 0 < m := by
    exact lt_of_lt_of_le hb0 hbm
  have hkNat : m < b ^ (k + 1) := by
    simpa [k, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hb1 m
  have hm1_le_nat : m + 1 ≤ b ^ (k + 1) := by
    exact Nat.succ_le_of_lt hkNat
  have hbpow_pos : (0 : ℝ) < (b : ℝ) ^ (k + 1) := by
    positivity
  have hlogm1_le' : Real.log (((m : ℕ) : ℝ) + 1) ≤ Real.log ((b : ℝ) ^ (k + 1)) := by
    refine (Real.log_le_log_iff hm1R0 hbpow_pos).2 ?_
    exact_mod_cast hm1_le_nat
  have hlogm1_le : Real.log (((m : ℕ) : ℝ) + 1) ≤ (((k : ℕ) : ℝ) + 1) * Real.log b := by
    simpa [Nat.cast_add, Nat.cast_one, k] using hlogm1_le'
  have hloglogb_lt : Real.log (Real.log b) < Real.log b := by
    exact Real.log_lt_log hlogb_pos hlogb_lt_b
  have hfinal : Real.log (Real.log x) < ((((k : ℕ) : ℝ) + 2) * Real.log b) := by
    linarith
  simpa [m, k] using hfinal

theorem doubleMacro_density_lower_aux (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) : (1 / (3 * Real.log b)) * Real.log (Real.log x) ≤ (((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 1) := by
  have hb1 : 1 < b := by
    omega
  have hlogb : 0 < Real.log b := by
    have hb1R : (1 : ℝ) < b := by
      exact_mod_cast hb1
    exact Real.log_pos hb1R
  have hk0 : 0 ≤ ((Nat.log b (Nat.log b x) : ℕ) : ℝ) := by
    positivity
  have hbound : Real.log (Real.log x) ≤ ((((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 2) * Real.log b) := by
    exact le_of_lt (doubleMacro_log_upper_bound b x hb hx)
  have hmain : Real.log (Real.log x) ≤ ((((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 1) * (3 * Real.log b)) := by
    nlinarith [hbound, hlogb, hk0]
  have hden : 0 < 3 * Real.log b := by
    nlinarith [hlogb]
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ hden).2 hmain

theorem doubleMacro_loglog_base_pos (b : ℕ) (hb : 2 ≤ b) : 0 < Real.log ((b : ℝ) * Real.log b) := by
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (le_trans (by norm_num) hb)
  have h2le : (2 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hb
  have hmul : Real.log 2 * (2 : ℝ) ≤ Real.log (b : ℝ) * (b : ℝ) := by
    exact Real.log_mul_self_monotoneOn (by norm_num) hb1 h2le
  have hlog2 : (1 : ℝ) < 2 * Real.log 2 := by
    have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith
  have hgt1 : (1 : ℝ) < (b : ℝ) * Real.log b := by
    have hmul' : (2 : ℝ) * Real.log 2 ≤ (b : ℝ) * Real.log b := by
      simpa [mul_comm] using hmul
    linarith
  exact Real.log_pos hgt1

theorem doubleMacro_loglog_ge_base (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) : Real.log ((b : ℝ) * Real.log b) ≤ Real.log (Real.log x) := by
  have hb1 : (1 : ℝ) < b := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log b := by
    exact Real.log_pos hb1
  have hpow : (b : ℝ) ^ b ≤ x := by
    exact_mod_cast hx
  have hlogx : (b : ℝ) * Real.log b ≤ Real.log x := by
    simpa only [Real.log_pow] using Real.le_log_of_pow_le hb0 hpow
  have hmul_pos : 0 < (b : ℝ) * Real.log b := by
    exact mul_pos hb0 hlogb
  have hxlog_pos : 0 < Real.log x := by
    exact lt_of_lt_of_le hmul_pos hlogx
  exact Real.log_le_log hmul_pos hlogx

theorem doubleMacro_density_upper_aux (b x : ℕ) (hb : 2 ≤ b) (hx : x ≥ b ^ b) : (((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 1) ≤ (1 / Real.log b + 2 / Real.log ((b : ℝ) * Real.log b)) * Real.log (Real.log x) := by
  let k : ℝ := (Nat.log b (Nat.log b x) : ℕ)
  let L : ℝ := Real.log (Real.log x)
  let d : ℝ := Real.log ((b : ℝ) * Real.log b)
  have h1 : (k - 1) * Real.log b ≤ L := by
    simpa [k, L] using doubleMacro_log_lower_bound b x hb hx
  have hbasepos : 0 < d := by
    simpa [d] using doubleMacro_loglog_base_pos b hb
  have hbasele : d ≤ L := by
    simpa [d, L] using doubleMacro_loglog_ge_base b x hb hx
  have hb1 : (1 : ℝ) < b := by
    exact_mod_cast (lt_of_lt_of_le (show (1 : ℕ) < 2 by decide) hb)
  have hlogb : 0 < Real.log b := by
    exact Real.log_pos hb1
  have hdivk : k - 1 ≤ L / Real.log b := by
    exact (le_div_iff₀ hlogb).2 h1
  have hk : k + 1 ≤ L / Real.log b + 2 := by
    linarith
  have hdiv : (1 : ℝ) ≤ L / d := by
    have htmp : (1 : ℝ) * d ≤ L := by
      simpa using hbasele
    exact (le_div_iff₀ hbasepos).2 htmp
  have hL2' : (2 : ℝ) ≤ 2 * (L / d) := by
    have := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
    simpa [two_mul] using this
  have hL2 : (2 : ℝ) ≤ (2 / d) * L := by
    calc
      (2 : ℝ) ≤ 2 * (L / d) := hL2'
      _ = (2 / d) * L := by ring
  have hsum : k + 1 ≤ L / Real.log b + (2 / d) * L := by
    linarith
  calc
    (((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 1) = k + 1 := by simp [k]
    _ ≤ L / Real.log b + (2 / d) * L := hsum
    _ = (1 / Real.log b + 2 / d) * L := by ring
    _ = (1 / Real.log b + 2 / Real.log ((b : ℝ) * Real.log b)) * Real.log (Real.log x) := by simp [L, d]

theorem doubleMacro_lower_radius_bound (b s k : ℕ) (hb : 2 ≤ b) (hk1 : 2 * (doubleMacroNat b k) ^ (b - 1) ≤ s) (hk2 : s < 2 * (doubleMacroNat b (k + 1)) ^ (b - 1)) : (1 / 64 : ℝ) * Real.rpow s ((b : ℝ) / (b - 1)) ≤ (s - 2 * (doubleMacroNat b k) ^ (b - 1)) * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1) := by
  set m0 : ℕ := doubleMacroNat b k
  set m1 : ℕ := doubleMacroNat b (k + 1)
  set α : ℝ := (b : ℝ) / ((b : ℝ) - 1)
  have hbpos : 0 < b := by omega
  have hb1R : 0 < (b : ℝ) - 1 := by
    have h1 : (1 : ℝ) < b := by
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hb)
    linarith
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos (by exact_mod_cast hbpos) hb1R
  have hαnonneg : 0 ≤ α := le_of_lt hαpos
  have hαmul : α * ((b : ℝ) - 1) = b := by
    dsimp [α]
    field_simp [hb1R.ne']
  have hαle2 : α ≤ 2 := by
    have hbR : (2 : ℝ) ≤ b := by
      exact_mod_cast hb
    have htmp : b ≤ 2 * ((b : ℝ) - 1) := by
      nlinarith
    have hmulle : α * ((b : ℝ) - 1) ≤ 2 * ((b : ℝ) - 1) := by
      simpa [hαmul] using htmp
    nlinarith
  have hb_sub_cast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (show 1 ≤ b by omega))
  have hm0_two : 2 ≤ m0 := by
    have hpowpos : 0 < b ^ k := by
      exact Nat.pow_pos hbpos
    have hle : b ≤ b ^ (b ^ k) := Nat.le_pow hpowpos
    exact le_trans hb (by simpa [m0, doubleMacroNat] using hle)
  have hm1_two : 2 ≤ m1 := by
    have hpowpos : 0 < b ^ (k + 1) := by
      exact Nat.pow_pos hbpos
    have hle : b ≤ b ^ (b ^ (k + 1)) := Nat.le_pow hpowpos
    exact le_trans hb (by simpa [m1, doubleMacroNat] using hle)
  have hm1eq_nat : m1 = m0 ^ b := by
    simpa [m0, m1] using doubleMacroNat_succ b k
  have hm1eq : (m0 : ℝ) ^ b = (m1 : ℝ) := by
    exact_mod_cast hm1eq_nat.symm
  have hk1R : 2 * (m0 : ℝ) ^ (b - 1) ≤ (s : ℝ) := by
    exact_mod_cast hk1
  by_cases hs : s ≤ 4 * m0 ^ (b - 1)
  · have hsR : (s : ℝ) ≤ 4 * (m0 : ℝ) ^ (b - 1) := by
      exact_mod_cast hs
    have h_rpow_le : Real.rpow (s : ℝ) α ≤ Real.rpow (4 * (m0 : ℝ) ^ (b - 1)) α := by
      exact Real.rpow_le_rpow (by positivity) hsR hαnonneg
    have h4α_le : Real.rpow (4 : ℝ) α ≤ 16 := by
      calc
        Real.rpow (4 : ℝ) α ≤ Real.rpow (4 : ℝ) (2 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hαle2
        _ = 16 := by
          norm_num [Real.rpow_natCast]
    have hm0pow : Real.rpow ((m0 : ℝ) ^ (b - 1)) α = (m0 : ℝ) ^ b := by
      have hmul : ((b - 1 : ℕ) : ℝ) * α = b := by
        rw [hb_sub_cast]
        nlinarith [hαmul]
      simpa [hmul] using
        (Real.rpow_natCast_mul (x := (m0 : ℝ)) (n := b - 1) (z := α) (by positivity)).symm
    have h_upper : Real.rpow (4 * (m0 : ℝ) ^ (b - 1)) α ≤ 16 * (m1 : ℝ) := by
      calc
        Real.rpow (4 * (m0 : ℝ) ^ (b - 1)) α
            = Real.rpow (4 : ℝ) α * Real.rpow ((m0 : ℝ) ^ (b - 1)) α := by
                simpa using
                  (Real.mul_rpow (x := (4 : ℝ)) (y := (m0 : ℝ) ^ (b - 1)) (z := α)
                    (by positivity) (by positivity))
        _ = Real.rpow (4 : ℝ) α * (m0 : ℝ) ^ b := by
              rw [hm0pow]
        _ ≤ 16 * (m0 : ℝ) ^ b := by
              exact mul_le_mul_of_nonneg_right h4α_le (by positivity)
        _ = 16 * (m1 : ℝ) := by
              rw [hm1eq]
    have h_lhs_le : (1 / 64 : ℝ) * Real.rpow (s : ℝ) α ≤ (m1 : ℝ) / 4 := by
      calc
        (1 / 64 : ℝ) * Real.rpow (s : ℝ) α
            ≤ (1 / 64 : ℝ) * Real.rpow (4 * (m0 : ℝ) ^ (b - 1)) α := by
                exact mul_le_mul_of_nonneg_left h_rpow_le (by positivity)
        _ ≤ (1 / 64 : ℝ) * (16 * (m1 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left h_upper (by positivity)
        _ = (m1 : ℝ) / 4 := by
              ring
    have hsub_nonneg : 0 ≤ (s : ℝ) - 2 * (m0 : ℝ) ^ (b - 1) := by
      linarith
    have hfirst_nonneg : 0 ≤ ((s : ℝ) - 2 * (m0 : ℝ) ^ (b - 1)) * (m1 : ℝ) := by
      exact mul_nonneg hsub_nonneg (by positivity)
    have h_rhs_lower : (m1 : ℝ) / 4 ≤
        ((s : ℝ) - 2 * (m0 : ℝ) ^ (b - 1)) * (m1 : ℝ) + ((m1 : ℝ) - 1) := by
      have hm1R : (2 : ℝ) ≤ (m1 : ℝ) := by
        exact_mod_cast hm1_two
      nlinarith
    exact le_trans h_lhs_le h_rhs_lower
  · have hs' : 4 * m0 ^ (b - 1) < s := by
      exact lt_of_not_ge hs
    have hs'R : (4 : ℝ) * (m0 : ℝ) ^ (b - 1) < (s : ℝ) := by
      exact_mod_cast hs'
    have hsub_half : (s : ℝ) / 2 ≤ (s : ℝ) - 2 * (m0 : ℝ) ^ (b - 1) := by
      nlinarith
    have h_rhs_lower : (s : ℝ) / 2 * (m1 : ℝ) ≤
        ((s : ℝ) - 2 * (m0 : ℝ) ^ (b - 1)) * (m1 : ℝ) + ((m1 : ℝ) - 1) := by
      have hm1_nonneg : 0 ≤ (m1 : ℝ) := by positivity
      have hmul : (s : ℝ) / 2 * (m1 : ℝ) ≤ ((s : ℝ) - 2 * (m0 : ℝ) ^ (b - 1)) * (m1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hsub_half hm1_nonneg
      have hsecond_nonneg : 0 ≤ (m1 : ℝ) - 1 := by
        have hm1R : (2 : ℝ) ≤ (m1 : ℝ) := by
          exact_mod_cast hm1_two
        linarith
      nlinarith
    have hs_half_lt : (s : ℝ) / 2 < (m1 : ℝ) ^ (b - 1) := by
      have hk2R : (s : ℝ) < 2 * (m1 : ℝ) ^ (b - 1) := by
        exact_mod_cast hk2
      nlinarith
    have hroot_lt : Real.rpow ((s : ℝ) / 2) (((b : ℝ) - 1)⁻¹) < (m1 : ℝ) := by
      have hpow_lt :=
        Real.rpow_lt_rpow (by positivity : 0 ≤ (s : ℝ) / 2) hs_half_lt
          (by positivity : 0 < ((b : ℝ) - 1)⁻¹)
      exact lt_of_lt_of_eq hpow_lt (by
        have hmul : ((b - 1 : ℕ) : ℝ) * (((b : ℝ) - 1)⁻¹) = 1 := by
          rw [hb_sub_cast]
          field_simp [hb1R.ne']
        symm
        simpa [hmul] using
          (Real.rpow_natCast_mul (x := (m1 : ℝ)) (n := b - 1) (z := (((b : ℝ) - 1)⁻¹))
            (by positivity)))
    have hα_eq : α = (((b : ℝ) - 1)⁻¹) + 1 := by
      dsimp [α]
      field_simp [hb1R.ne']
      ring
    have h_half_eq : Real.rpow ((s : ℝ) / 2) α =
        Real.rpow ((s : ℝ) / 2) (((b : ℝ) - 1)⁻¹) * ((s : ℝ) / 2) := by
      have hsum_ne : (((b : ℝ) - 1)⁻¹) + ((1 : ℕ) : ℝ) ≠ 0 := by
        positivity
      simpa [hα_eq, Real.rpow_natCast, mul_comm, mul_left_comm, mul_assoc] using
        (Real.rpow_add_natCast' (x := (s : ℝ) / 2) (y := (((b : ℝ) - 1)⁻¹)) (n := 1)
          (by positivity : 0 ≤ (s : ℝ) / 2) hsum_ne)
    have hsHalfPos : 0 < (s : ℝ) / 2 := by
      have hleftpos : 0 < (4 : ℝ) * (m0 : ℝ) ^ (b - 1) := by
        positivity
      have hspos : 0 < (s : ℝ) := lt_trans hleftpos hs'R
      nlinarith
    have h_half_lt : Real.rpow ((s : ℝ) / 2) α < (s : ℝ) / 2 * (m1 : ℝ) := by
      calc
        Real.rpow ((s : ℝ) / 2) α
            = Real.rpow ((s : ℝ) / 2) (((b : ℝ) - 1)⁻¹) * ((s : ℝ) / 2) := h_half_eq
        _ < (m1 : ℝ) * ((s : ℝ) / 2) := by
            exact mul_lt_mul_of_pos_right hroot_lt hsHalfPos
        _ = (s : ℝ) / 2 * (m1 : ℝ) := by ring
    have hquarter_le : (1 / 4 : ℝ) ≤ Real.rpow (1 / 2 : ℝ) α := by
      have htmp : Real.rpow (1 / 2 : ℝ) (2 : ℝ) ≤ Real.rpow (1 / 2 : ℝ) α := by
        exact Real.rpow_le_rpow_of_exponent_ge' (by positivity) (by norm_num) hαnonneg hαle2
      calc
        (1 / 4 : ℝ) = Real.rpow (1 / 2 : ℝ) (2 : ℝ) := by
          norm_num [Real.rpow_natCast]
        _ ≤ Real.rpow (1 / 2 : ℝ) α := htmp
    have h_half_pow_eq : Real.rpow ((s : ℝ) / 2) α =
        Real.rpow (s : ℝ) α * Real.rpow (1 / 2 : ℝ) α := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (Real.mul_rpow (x := (s : ℝ)) (y := (1 / 2 : ℝ)) (z := α) (by positivity) (by positivity))
    have hs_nonneg : 0 ≤ Real.rpow (s : ℝ) α := by
      exact Real.rpow_nonneg (by positivity) _
    have hquarter_mul : (1 / 4 : ℝ) * Real.rpow (s : ℝ) α ≤ Real.rpow ((s : ℝ) / 2) α := by
      have htmp := mul_le_mul_of_nonneg_left hquarter_le hs_nonneg
      calc
        (1 / 4 : ℝ) * Real.rpow (s : ℝ) α = Real.rpow (s : ℝ) α * (1 / 4 : ℝ) := by ring
        _ ≤ Real.rpow (s : ℝ) α * Real.rpow (1 / 2 : ℝ) α := htmp
        _ = Real.rpow ((s : ℝ) / 2) α := h_half_pow_eq.symm
    have hsmallconst : (1 / 64 : ℝ) * Real.rpow (s : ℝ) α ≤ (1 / 4 : ℝ) * Real.rpow (s : ℝ) α := by
      exact mul_le_mul_of_nonneg_right (by norm_num : (1 / 64 : ℝ) ≤ 1 / 4) hs_nonneg
    have hmain : (1 / 64 : ℝ) * Real.rpow (s : ℝ) α < (s : ℝ) / 2 * (m1 : ℝ) := by
      exact lt_of_le_of_lt (le_trans hsmallconst hquarter_mul) h_half_lt
    exact le_trans (le_of_lt hmain) h_rhs_lower

theorem doubleMacro_single_macro_mem (b k : ℕ) : Multiset.replicate (doubleMacroNat b k) (0 : Fin 1) ∈ DoublyMacroSet b ∪ A 1 := by
  left
  refine ⟨0, k, ?_⟩
  rfl

theorem doubleMacro_k_macro_mem_ball (b k q : ℕ) : Multiset.replicate (q * doubleMacroNat b k) (0 : Fin 1) ∈ Ball q (DoublyMacroSet b ∪ A 1) := by
  refine ⟨List.replicate q (Multiset.replicate (doubleMacroNat b k) (0 : Fin 1)), ?_, ?_, ?_⟩
  · simp
  · intro x hx
    rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
    exact doubleMacro_single_macro_mem b k
  · rw [List.sum_replicate, Multiset.nsmul_replicate]

theorem doubleMacro_q_macro_mem_ball (b k q : ℕ) : Multiset.replicate (q * doubleMacroNat b (k + 1)) (0 : Fin 1) ∈ Ball q (DoublyMacroSet b ∪ A 1) := by
  refine ⟨List.replicate q (Multiset.replicate (doubleMacroNat b (k + 1)) (0 : Fin 1)), ?_, ?_, ?_⟩
  · rw [List.length_replicate]
  · intro x hx
    rw [List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩
    exact doubleMacro_single_macro_mem b (k + 1)
  · simpa only [List.sum_replicate, Multiset.nsmul_replicate]

theorem doubleMacro_small_ball_mem (b k x : ℕ) (hb : 2 ≤ b) : x < doubleMacroNat b (k + 1) → Multiset.replicate x (0 : Fin 1) ∈ Ball (2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) := by
  induction k generalizing x with
  | zero =>
      intro hx
      let q := x / b
      let r := x % b
      have hq_ball : Multiset.replicate (q * b) (0 : Fin 1) ∈
          Ball q (DoublyMacroSet b ∪ A 1) := by
        refine ⟨List.replicate q (Multiset.replicate b (0 : Fin 1)), ?_, ?_, ?_⟩
        · simp
        · intro m hm
          left
          have hm_eq : m = Multiset.replicate b (0 : Fin 1) := (List.mem_replicate.mp hm).2
          rw [hm_eq]
          refine ⟨(0 : Fin 1), 0, ?_⟩
          simp [DoublyMacroSet]
        · simp [List.sum_replicate, Multiset.nsmul_replicate, Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc]
      have hr_ball : Multiset.replicate r (0 : Fin 1) ∈
          Ball r (DoublyMacroSet b ∪ A 1) := by
        refine ⟨List.replicate r ({(0 : Fin 1)} : Multiset (Fin 1)), ?_, ?_, ?_⟩
        · simp
        · intro m hm
          right
          have hm_eq : m = ({(0 : Fin 1)} : Multiset (Fin 1)) := (List.mem_replicate.mp hm).2
          rw [hm_eq]
          exact ⟨(0 : Fin 1), rfl⟩
        · simpa using (Multiset.nsmul_replicate (a := (0 : Fin 1)) r 1)
      have hsum_eq :
          Multiset.replicate (q * b) (0 : Fin 1) + Multiset.replicate r (0 : Fin 1) =
            Multiset.replicate x (0 : Fin 1) := by
        rw [← Multiset.replicate_add]
        simp [q, r, Nat.div_add_mod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hsum_ball0 :
          Multiset.replicate (q * b) (0 : Fin 1) + Multiset.replicate r (0 : Fin 1) ∈
            Ball (q + r) (DoublyMacroSet b ∪ A 1) :=
        Ball_add_A1 hq_ball hr_ball
      have hsum_ball : Multiset.replicate x (0 : Fin 1) ∈
          Ball (q + r) (DoublyMacroSet b ∪ A 1) := by
        rw [hsum_eq] at hsum_ball0
        exact hsum_ball0
      rcases hsum_ball with ⟨l, hl, hlX, hlsum⟩
      refine ⟨l, ?_, hlX, hlsum⟩
      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
      have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
      have hq_lt : q < b ^ (b - 1) := by
        apply (Nat.div_lt_iff_lt_mul hbpos).2
        rw [Nat.pow_pred_mul hbpos]
        simpa [doubleMacroNat, q] using hx
      have hq_le : q ≤ b ^ (b - 1) := Nat.le_of_lt hq_lt
      have hr_lt : r < b := by
        simpa [r] using (Nat.mod_lt x hbpos)
      have hbm1 : 1 ≤ b - 1 := by
        omega
      have hpow_ge_b : b ≤ b ^ (b - 1) := by
        calc
          b = b ^ 1 := by simp
          _ ≤ b ^ (b - 1) := by
            exact pow_le_pow_right' hb1 hbm1
      have hr_le : r ≤ b ^ (b - 1) := Nat.le_of_lt (lt_of_lt_of_le hr_lt hpow_ge_b)
      have hcost : q + r ≤ 2 * (doubleMacroNat b 0) ^ (b - 1) := by
        calc
          q + r ≤ b ^ (b - 1) + b ^ (b - 1) := Nat.add_le_add hq_le hr_le
          _ = 2 * b ^ (b - 1) := by simp [two_mul]
          _ = 2 * (doubleMacroNat b 0) ^ (b - 1) := by simp [doubleMacroNat]
      exact le_trans hl hcost
  | succ k ih =>
      intro hx
      let a := doubleMacroNat b (k + 1)
      let q := x / a
      let r := x % a
      have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
      have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
      have hapos : 0 < a := by
        simpa [a, doubleMacroNat] using (pow_pos hbpos (b ^ (k + 1)))
      have hq_ball : Multiset.replicate (q * a) (0 : Fin 1) ∈
          Ball q (DoublyMacroSet b ∪ A 1) := by
        simpa [a, q] using (doubleMacro_q_macro_mem_ball b k q)
      have hr_lt : r < a := by
        simpa [r] using (Nat.mod_lt x hapos)
      have hr_ball : Multiset.replicate r (0 : Fin 1) ∈
          Ball (2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) := by
        exact ih r hr_lt
      have hsum_eq :
          Multiset.replicate (q * a) (0 : Fin 1) + Multiset.replicate r (0 : Fin 1) =
            Multiset.replicate x (0 : Fin 1) := by
        rw [← Multiset.replicate_add]
        simp [q, r, Nat.div_add_mod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hsum_ball0 :
          Multiset.replicate (q * a) (0 : Fin 1) + Multiset.replicate r (0 : Fin 1) ∈
            Ball (q + 2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) :=
        Ball_add_A1 hq_ball hr_ball
      have hsum_ball : Multiset.replicate x (0 : Fin 1) ∈
          Ball (q + 2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) := by
        rw [hsum_eq] at hsum_ball0
        exact hsum_ball0
      rcases hsum_ball with ⟨l, hl, hlX, hlsum⟩
      refine ⟨l, ?_, hlX, hlsum⟩
      have hq_lt : q < a ^ (b - 1) := by
        apply (Nat.div_lt_iff_lt_mul hapos).2
        rw [Nat.pow_pred_mul hbpos]
        simpa [a, doubleMacroNat_succ] using hx
      have hq_le : q ≤ a ^ (b - 1) := Nat.le_of_lt hq_lt
      have hkge2 : 2 ≤ doubleMacroNat b k := by
        calc
          2 ≤ b := hb
          _ ≤ b ^ (b ^ k) := by
            have hbkpos : 0 < b ^ k := pow_pos hbpos k
            have hbk1 : 1 ≤ b ^ k := Nat.succ_le_of_lt hbkpos
            calc
              b = b ^ 1 := by simp
              _ ≤ b ^ (b ^ k) := by
                exact pow_le_pow_right' hb1 hbk1
          _ = doubleMacroNat b k := by simp [doubleMacroNat]
      have hrem_le_a : 2 * (doubleMacroNat b k) ^ (b - 1) ≤ a := by
        calc
          2 * (doubleMacroNat b k) ^ (b - 1)
              ≤ (doubleMacroNat b k) * (doubleMacroNat b k) ^ (b - 1) := by
                exact Nat.mul_le_mul_right ((doubleMacroNat b k) ^ (b - 1)) hkge2
          _ = (doubleMacroNat b k) ^ b := by
                rw [Nat.mul_comm]
                rw [Nat.pow_pred_mul hbpos]
          _ = a := by simpa [a] using (doubleMacroNat_succ b k).symm
      have hbm1 : 1 ≤ b - 1 := by
        omega
      have ha1 : 1 ≤ a := Nat.succ_le_of_lt hapos
      have ha_le_pow : a ≤ a ^ (b - 1) := by
        calc
          a = a ^ 1 := by simp
          _ ≤ a ^ (b - 1) := by
            exact pow_le_pow_right' ha1 hbm1
      have hrem_le : 2 * (doubleMacroNat b k) ^ (b - 1) ≤ a ^ (b - 1) := le_trans hrem_le_a ha_le_pow
      have hcost : q + 2 * (doubleMacroNat b k) ^ (b - 1) ≤
          2 * (doubleMacroNat b (k + 1)) ^ (b - 1) := by
        calc
          q + 2 * (doubleMacroNat b k) ^ (b - 1)
              ≤ a ^ (b - 1) + a ^ (b - 1) := Nat.add_le_add hq_le hrem_le
          _ = 2 * a ^ (b - 1) := by simp [two_mul]
          _ = 2 * (doubleMacroNat b (k + 1)) ^ (b - 1) := by simp [a]
      exact le_trans hl hcost

theorem fa1_eq_replicate_card (m : FreeAbelianMonoid 1) : m = Multiset.replicate m.card (0 : Fin 1) := by
  ext a
  by_cases h : a = (0 : Fin 1)
  · subst h
    simp
    exact (Multiset.count_eq_card).2 (by
      intro x hx
      exact (Fin.eq_zero x).symm)
  · exfalso
    exact h (Fin.eq_zero a)

theorem ball_A1_iff_card_le (R : ℕ) (m : FreeAbelianMonoid 1) : m ∈ Ball R (A 1) ↔ m.card ≤ R := by
  constructor
  · rintro ⟨l, hlR, hlA, hsum⟩
    have hsum_card :
        ∀ l : List (FreeAbelianMonoid 1), (∀ x, x ∈ l → x ∈ A 1) → l.sum.card = l.length := by
      intro l
      induction l with
      | nil =>
          intro hA
          simp
      | cons x xs ih =>
          intro hA
          have hAx : ∃ i : Fin 1, x = ({i} : FreeAbelianMonoid 1) := by
            simpa [A] using hA x (by simp)
          rcases hAx with ⟨i, rfl⟩
          have hxsA : ∀ y, y ∈ xs → y ∈ A 1 := by
            intro y hy
            exact hA y (by simp [hy])
          calc
            ({i} :: xs).sum.card = ({i} + xs.sum).card := by simp
            _ = ({i} : FreeAbelianMonoid 1).card + xs.sum.card := by rw [Multiset.card_add]
            _ = 1 + xs.length := by rw [Multiset.card_singleton, ih hxsA]
            _ = ({i} :: xs).length := by simpa [Nat.add_comm]
    calc
      m.card = l.sum.card := by rw [← hsum]
      _ = l.length := hsum_card l hlA
      _ ≤ R := hlR
  · intro hm
    refine ⟨List.replicate m.card ({(0 : Fin 1)} : FreeAbelianMonoid 1), ?_, ?_, ?_⟩
    · simpa using hm
    · intro x hx
      have hx' : x = ({(0 : Fin 1)} : FreeAbelianMonoid 1) := by
        exact List.eq_of_mem_replicate hx
      rw [hx']
      simpa [A]
    · rw [List.sum_replicate, Multiset.nsmul_singleton]
      exact (fa1_eq_replicate_card m).symm

theorem doubleMacro_cover_linear (b k q : ℕ) (hb : 2 ≤ b) : Ball (q * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1)) (A 1) ⊆ Ball (q + 2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) := by
  intro m hm
  have hmcard : m.card ≤ q * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1) :=
    (ball_A1_iff_card_le (q * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1)) m).1 hm
  have hmrep : m = Multiset.replicate m.card (0 : Fin 1) := fa1_eq_replicate_card m
  let D := doubleMacroNat b (k + 1)
  let q' := m.card / D
  let r := m.card % D
  have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hb
  have hDpos : 0 < D := by
    dsimp [D, doubleMacroNat]
    exact pow_pos hbpos _
  have hrlt : r < D := by
    dsimp [r]
    exact Nat.mod_lt _ hDpos
  have hdecomp : m.card = q' * D + r := by
    dsimp [q', r]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.div_add_mod m.card D).symm
  have hlt_bound : m.card < (q + 1) * D := by
    have h1 : q * D + (D - 1) < q * D + D := by
      exact Nat.add_lt_add_left (Nat.sub_lt hDpos (by decide : 0 < (1 : ℕ))) (q * D)
    have h2 : m.card < q * D + D := lt_of_le_of_lt hmcard h1
    calc
      m.card < q * D + D := h2
      _ = (q + 1) * D := by rw [Nat.add_mul, Nat.one_mul]
  have hq'lt : q' < q + 1 := by
    dsimp [q']
    exact (Nat.div_lt_iff_lt_mul hDpos).2 hlt_bound
  have hqle : q' ≤ q := Nat.lt_succ_iff.mp hq'lt
  have hmacro : Multiset.replicate (q' * D) (0 : Fin 1) ∈ Ball q' (DoublyMacroSet b ∪ A 1) := by
    simpa [D] using doubleMacro_q_macro_mem_ball b k q'
  have hrem : Multiset.replicate r (0 : Fin 1) ∈ Ball (2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) :=
    doubleMacro_small_ball_mem b k r hb hrlt
  have hsum : Multiset.replicate m.card (0 : Fin 1) = Multiset.replicate (q' * D) (0 : Fin 1) + Multiset.replicate r (0 : Fin 1) := by
    rw [← Multiset.replicate_add]
    simpa [hdecomp]
  have hadd : Multiset.replicate m.card (0 : Fin 1) ∈ Ball (q' + 2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) := by
    rw [hsum]
    exact Ball_add_A1 hmacro hrem
  have hlen : q' + 2 * (doubleMacroNat b k) ^ (b - 1) ≤ q + 2 * (doubleMacroNat b k) ^ (b - 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      add_le_add_right hqle (2 * (doubleMacroNat b k) ^ (b - 1))
  have hfinal : Multiset.replicate m.card (0 : Fin 1) ∈ Ball (q + 2 * (doubleMacroNat b k) ^ (b - 1)) (DoublyMacroSet b ∪ A 1) := by
    rcases hadd with ⟨l, hl, hlX, hlsum⟩
    exact ⟨l, le_trans hl hlen, hlX, hlsum⟩
  rw [hmrep]
  exact hfinal

theorem doublyMacroSet_card_iff (b : ℕ) {m : FreeAbelianMonoid 1} : m ∈ DoublyMacroSet b ↔ ∃ j : ℕ, m.card = doubleMacroNat b j := by
  constructor
  · intro hm
    rcases hm with ⟨i, j, rfl⟩
    refine ⟨j, ?_⟩
    simp [doubleMacroNat]
  · rintro ⟨j, hj⟩
    refine ⟨0, j, ?_⟩
    rw [fa1_eq_replicate_card m, hj]
    rfl

theorem doubleMacro_inter_ball_ncard (b x : ℕ) (hb : 2 ≤ b) (hx : b ≤ x) : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 := by
  classical
  let N := Nat.log b (Nat.log b x)
  have hb' : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb
  have hx0 : x ≠ 0 := by
    apply Nat.ne_of_gt
    exact lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 2) hb) hx
  have hlogx0 : Nat.log b x ≠ 0 := by
    apply Nat.ne_of_gt
    exact (Nat.log_pos_iff).2 ⟨hx, hb'⟩
  have hcongr : (Set.Iic N).ncard = (DoublyMacroSet b ∩ Ball x (A 1)).ncard := by
    refine Set.ncard_congr (s := Set.Iic N) (t := DoublyMacroSet b ∩ Ball x (A 1))
      (fun j _ => Multiset.replicate (doubleMacroNat b j) (0 : Fin 1)) ?_ ?_ ?_
    · intro j hj
      constructor
      · rw [doublyMacroSet_card_iff]
        exact ⟨j, by simp [doubleMacroNat]⟩
      · rw [ball_A1_iff_card_le]
        have hpow1 : b ^ j ≤ Nat.log b x := Nat.pow_le_of_le_log hlogx0 hj
        have hpow2 : doubleMacroNat b j ≤ x := by
          simpa [doubleMacroNat] using (Nat.pow_le_of_le_log hx0 hpow1)
        simpa [doubleMacroNat] using hpow2
    · intro j k hj hk hEq
      have h1 : doubleMacroNat b j = doubleMacroNat b k := by
        simpa using congrArg Multiset.card hEq
      have h2 : b ^ j = b ^ k := by
        have := congrArg (Nat.log b) h1
        simpa [doubleMacroNat, Nat.log_pow hb'] using this
      have h3 : j = k := by
        have := congrArg (Nat.log b) h2
        simpa [Nat.log_pow hb'] using this
      exact h3
    · intro m hm
      have hmD : m ∈ DoublyMacroSet b := hm.1
      have hmB : m ∈ Ball x (A 1) := hm.2
      rw [doublyMacroSet_card_iff] at hmD
      rw [ball_A1_iff_card_le] at hmB
      obtain ⟨j, hjcard⟩ := hmD
      have hpow : doubleMacroNat b j ≤ x := by
        simpa [hjcard] using hmB
      have hpow1 : b ^ j ≤ Nat.log b x := by
        exact Nat.le_log_of_pow_le hb' (by simpa [doubleMacroNat] using hpow)
      have hjN : j ≤ N := by
        exact Nat.le_log_of_pow_le hb' hpow1
      have hmrep : m = Multiset.replicate m.card (0 : Fin 1) := by
        refine Multiset.eq_replicate_of_mem ?_
        intro i hi
        exact Subsingleton.elim _ _
      refine ⟨j, hjN, ?_⟩
      calc
        Multiset.replicate (doubleMacroNat b j) (0 : Fin 1)
            = Multiset.replicate m.card (0 : Fin 1) := by rw [← hjcard]
        _ = m := hmrep.symm
  have hIicset : (Set.Iic N : Set ℕ) = (((Finset.Iic N : Finset ℕ) : Set ℕ)) := by
    ext n
    simp
  have hIic : (Set.Iic N : Set ℕ).ncard = N + 1 := by
    calc
      (Set.Iic N : Set ℕ).ncard = (((Finset.Iic N : Finset ℕ) : Set ℕ)).ncard := by rw [hIicset]
      _ = (Finset.Iic N).card := Set.ncard_coe_finset _
      _ = N + 1 := Nat.card_Iic N
  have : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = N + 1 := by
    omega
  simpa [N] using this

theorem doublyMacro_mem_prefix_of_card_lt (b K : ℕ) (hb : 2 ≤ b) {m : FreeAbelianMonoid 1} : m ∈ DoublyMacroSet b → m.card < doubleMacroNat b (K + 1) → m ∈ (↑(doubleMacroPrefix b K) : Set (FreeAbelianMonoid 1)) := by
  intro hm hlt
  rcases (show ∃ i : Fin 1, ∃ j : ℕ, m = Multiset.replicate (doubleMacroNat b j) i from by
    simpa [DoublyMacroSet, doubleMacroNat] using hm) with ⟨i, j, rfl⟩
  have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  have hjle : j ≤ K := by
    by_contra hjle
    have hK1le : K + 1 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_not_ge hjle)
    have hmono : doubleMacroNat b (K + 1) ≤ doubleMacroNat b j :=
      doubleMacroNat_mono b (K + 1) j hb hK1le
    have hge : doubleMacroNat b (K + 1) ≤ (Multiset.replicate (doubleMacroNat b j) (0 : Fin 1)).card := by
      simpa using hmono
    exact (not_lt_of_ge hge) hlt
  change Multiset.replicate (doubleMacroNat b j) (0 : Fin 1) ∈ doubleMacroPrefix b K
  unfold doubleMacroPrefix
  apply Finset.mem_image.2
  refine ⟨j, ?_, rfl⟩
  simpa [Finset.mem_range] using Nat.lt_succ_of_le hjle

def macroMaxCard1 (M : Finset (FreeAbelianMonoid 1)) : ℕ :=
  max (M.sup Multiset.card) 1

theorem card_le_mul_macroMax1 (M : Finset (FreeAbelianMonoid 1)) (s : ℕ) {m : FreeAbelianMonoid 1} : m ∈ Ball s ((↑M : Set (FreeAbelianMonoid 1)) ∪ A 1) → m.card ≤ s * macroMaxCard1 M := by
  intro hm
  classical
  rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩
  have hx_le : ∀ x : FreeAbelianMonoid 1, x ∈ l → x.card ≤ macroMaxCard1 M := by
    intro x hx
    have hxX : x ∈ ((↑M : Set (FreeAbelianMonoid 1)) ∪ A 1) := hl_mem x hx
    rcases hxX with hxM | hxA
    · have hle : x.card ≤ M.sup Multiset.card := by
        simpa using (Finset.le_sup (s := M) (f := Multiset.card) hxM)
      exact le_trans hle (by
        simpa [macroMaxCard1] using (le_max_left (M.sup Multiset.card) 1))
    · have hxA' : ∃ i : Fin 1, x = ({i} : FreeAbelianMonoid 1) := by
        simpa [A] using hxA
      rcases hxA' with ⟨i, rfl⟩
      simp [macroMaxCard1]
  have hcard : m.card = (l.map Multiset.card).sum := by
    have : Multiset.cardHom l.sum = (l.map Multiset.cardHom).sum := by
      simpa using (Multiset.cardHom.map_list_sum l)
    simpa [hl_sum] using this
  have hsum_le : (l.map Multiset.card).sum ≤ l.length * macroMaxCard1 M := by
    have hbound : ∀ n : ℕ, n ∈ l.map Multiset.card → n ≤ macroMaxCard1 M := by
      intro n hn
      rcases List.mem_map.1 hn with ⟨x, hx, rfl⟩
      exact hx_le x hx
    have h' := List.sum_le_card_nsmul (l := l.map Multiset.card) (n := macroMaxCard1 M) hbound
    simpa [Nat.nsmul_eq_mul] using h'
  calc
    m.card = (l.map Multiset.card).sum := hcard
    _ ≤ l.length * macroMaxCard1 M := hsum_le
    _ ≤ s * macroMaxCard1 M := by
      exact Nat.mul_le_mul_right (macroMaxCard1 M) hl_len

theorem doubleMacroPrefix_maxCard_le (b K : ℕ) (hb : 2 ≤ b) : macroMaxCard1 (doubleMacroPrefix b K) ≤ doubleMacroNat b K := by
  unfold macroMaxCard1 doubleMacroPrefix
  refine max_le ?_ ?_
  · refine Finset.sup_le ?_
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨j, hj, rfl⟩
    have hj' : j ≤ K := by
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simpa [doubleMacroNat] using doubleMacroNat_mono b j K hb hj'
  · unfold doubleMacroNat
    nlinarith [pow_pos (show 0 < b from lt_of_lt_of_le (by decide : 0 < 2) hb) (b ^ K)]

theorem doubleMacroPrefix_witness_not_mem (b K s : ℕ) (hb : 2 ≤ b) : Multiset.replicate (1 + s * doubleMacroNat b K) (0 : Fin 1) ∉ Ball s ((↑(doubleMacroPrefix b K) : Set (FreeAbelianMonoid 1)) ∪ A 1) := by
  intro hmem
  have hcard :
      (Multiset.replicate (1 + s * doubleMacroNat b K) (0 : Fin 1)).card ≤
        s * macroMaxCard1 (doubleMacroPrefix b K) :=
    card_le_mul_macroMax1 (doubleMacroPrefix b K) s hmem
  have hmax : macroMaxCard1 (doubleMacroPrefix b K) ≤ doubleMacroNat b K :=
    doubleMacroPrefix_maxCard_le b K hb
  have hle :
      (Multiset.replicate (1 + s * doubleMacroNat b K) (0 : Fin 1)).card ≤
        s * doubleMacroNat b K := by
    exact le_trans hcard (Nat.mul_le_mul_left s hmax)
  simp only [Multiset.card_replicate] at hle
  omega

theorem doubleMacro_full_witness_not_mem (b K s : ℕ) (hb : 2 ≤ b) (hsmall : 1 + s * doubleMacroNat b K < doubleMacroNat b (K + 1)) : Multiset.replicate (1 + s * doubleMacroNat b K) (0 : Fin 1) ∉ Ball s (DoublyMacroSet b ∪ A 1) := by
  intro hmem
  rcases hmem with ⟨l, hl_len, hl_mem, hl_sum⟩
  have hcardsum :
      (l.map Multiset.card).sum =
        (Multiset.replicate (1 + s * doubleMacroNat b K) (0 : Fin 1)).card := by
    simpa [hl_sum] using (Multiset.cardHom.map_list_sum l).symm
  have hprefix :
      Multiset.replicate (1 + s * doubleMacroNat b K) (0 : Fin 1) ∈
        Ball s ((↑(doubleMacroPrefix b K) : Set (FreeAbelianMonoid 1)) ∪ A 1) := by
    refine ⟨l, hl_len, ?_, hl_sum⟩
    intro m hm
    rcases hl_mem m hm with hmD | hmA
    · left
      have hmcard_lt : m.card < doubleMacroNat b (K + 1) := by
        have hmcard_le' : m.card ≤ 1 + s * doubleMacroNat b K := by
          calc
            m.card ≤ (l.map Multiset.card).sum := by
              exact List.le_sum_of_mem (List.mem_map_of_mem (f := Multiset.card) hm)
            _ = (Multiset.replicate (1 + s * doubleMacroNat b K) (0 : Fin 1)).card := hcardsum
            _ = 1 + s * doubleMacroNat b K := by simp
        exact lt_of_le_of_lt hmcard_le' hsmall
      exact doublyMacro_mem_prefix_of_card_lt (b := b) (K := K) hb hmD hmcard_lt
    · exact Or.inr hmA
  exact (doubleMacroPrefix_witness_not_mem b K s hb) hprefix

theorem theorem6_density_part (b : ℕ) (hb : 2 ≤ b) : ∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b ^ b) → 0 < d1 ∧ 0 < d2 ∧ d1 * (Real.log (Real.log x)) ≤ (DoublyMacroSet b ∩ Ball x (A 1)).ncard ∧ (DoublyMacroSet b ∩ Ball x (A 1)).ncard ≤ d2 * (Real.log (Real.log x)) := by
  let d1 : ℝ := 1 / (3 * Real.log b)
  let d2 : ℝ := 1 / Real.log b + 2 / Real.log ((b : ℝ) * Real.log b)
  refine ⟨d1, d2, ?_⟩
  intro x hx
  have hb1 : 1 < b := by
    omega
  have hlogb_pos : 0 < Real.log b := by
    exact Real.log_pos (by exact_mod_cast hb1)
  have hbpow : b ≤ b ^ b := by
    have hb0 : 0 < b := by omega
    have hpow : b ^ 1 ≤ b ^ b := by
      exact Nat.pow_le_pow_right hb0 (by omega)
    simpa using hpow
  have hx' : b ≤ x := by
    exact le_trans hbpow hx
  have hcount := doubleMacro_inter_ball_ncard b x hb hx'
  have hlower := doubleMacro_density_lower_aux b x hb hx
  have hupper := doubleMacro_density_upper_aux b x hb hx
  have hb2 : (2 : ℝ) ≤ b := by
    exact_mod_cast hb
  have hlog2_le : Real.log (2 : ℝ) ≤ Real.log b := by
    exact Real.log_le_log (by norm_num) hb2
  have h2logb : (1 : ℝ) < 2 * Real.log b := by
    have hmul : 2 * Real.log (2 : ℝ) ≤ 2 * Real.log b := by
      have htwo_nonneg : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left hlog2_le htwo_nonneg
    nlinarith [Real.log_two_gt_d9, hmul]
  have hbase_gt_one : 1 < (b : ℝ) * Real.log b := by
    have hmul : 2 * Real.log b ≤ (b : ℝ) * Real.log b := by
      exact mul_le_mul_of_nonneg_right hb2 (le_of_lt hlogb_pos)
    exact lt_of_lt_of_le h2logb hmul
  have hbase_pos : 0 < Real.log ((b : ℝ) * Real.log b) := by
    exact Real.log_pos hbase_gt_one
  have hd1 : 0 < d1 := by
    dsimp [d1]
    positivity
  have hd2 : 0 < d2 := by
    dsimp [d2]
    positivity
  have hcountR : ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ) =
      (((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 1) := by
    rw [hcount, Nat.cast_add, Nat.cast_one]
  refine ⟨hd1, hd2, ?_, ?_⟩
  · calc
      d1 * Real.log (Real.log x)
          = (1 / (3 * Real.log b)) * Real.log (Real.log x) := by rfl
      _ ≤ (((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 1) := hlower
      _ = ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ) := hcountR.symm
  · calc
      ((DoublyMacroSet b ∩ Ball x (A 1)).ncard : ℝ)
          = (((Nat.log b (Nat.log b x) : ℕ) : ℝ) + 1) := hcountR
      _ ≤ (1 / Real.log b + 2 / Real.log ((b : ℝ) * Real.log b)) * Real.log (Real.log x) := hupper
      _ = d2 * Real.log (Real.log x) := by rfl

theorem theorem6_expansion_lower_part (b : ℕ) (hb : 2 ≤ b) : ∃ C₁ B : ℝ, 0 < C₁ ∧ (∀ (s : ℕ), (s ≥ B) → let lb := Real.rpow s ((b : ℝ) / (b - 1)); Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ (A 1))) := by
  classical
  let C₁ : ℝ := (1 / 64 : ℝ)
  let B : ℝ := ((2 * (doubleMacroNat b 0) ^ (b - 1) : ℕ) : ℝ)
  refine ⟨C₁, B, ?_, ?_⟩
  · norm_num [C₁]
  · intro s hs
    let k : ℕ := Nat.findGreatest (fun j => 2 * (doubleMacroNat b j) ^ (b - 1) ≤ s) s
    let q : ℕ := s - 2 * (doubleMacroNat b k) ^ (b - 1)
    have hBreal : (((2 * (doubleMacroNat b 0) ^ (b - 1) : ℕ) : ℝ) ≤ s) := by
      simpa [B] using hs
    have hBnat : 2 * (doubleMacroNat b 0) ^ (b - 1) ≤ s := by
      exact_mod_cast hBreal
    have hscale := doubleMacro_find_scale_lower b s hb hBnat
    have hk1 : 2 * (doubleMacroNat b k) ^ (b - 1) ≤ s := by
      simpa [k] using hscale.1
    have hk2 : s < 2 * (doubleMacroNat b (k + 1)) ^ (b - 1) := by
      simpa [k] using hscale.2
    have hcover :
        Ball (q * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1)) (A 1) ⊆
          Ball s (DoublyMacroSet b ∪ A 1) := by
      have h := doubleMacro_cover_linear b k q hb
      have hq : q + 2 * (doubleMacroNat b k) ^ (b - 1) = s := by
        dsimp [q]
        omega
      simpa [hq] using h
    have hBall_mono :
        ∀ {r₁ r₂ : ℕ} {X : Set (FreeAbelianMonoid 1)}, r₁ ≤ r₂ → Ball r₁ X ⊆ Ball r₂ X := by
      intro r₁ r₂ X hr x hx
      rcases hx with ⟨l, hl, hmem, rfl⟩
      exact ⟨l, le_trans hl hr, hmem, rfl⟩
    have hrad :
        Int.toNat (Int.ceil (C₁ * Real.rpow s ((b : ℝ) / (b - 1)))) ≤
          q * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1) := by
      have hbound := doubleMacro_lower_radius_bound b s k hb hk1 hk2
      have hbpos : 0 < b := by
        omega
      have hm1 : 1 ≤ doubleMacroNat b (k + 1) := by
        simpa [doubleMacroNat] using Nat.one_le_pow (b ^ (k + 1)) b hbpos
      rw [Int.ceil_toNat]
      change Nat.ceil (C₁ * Real.rpow (s : ℝ) ((b : ℝ) / (b - 1))) ≤
        q * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1)
      rw [Nat.ceil_le]
      have hq_cast :
          (s : ℝ) - 2 * (doubleMacroNat b k : ℝ) ^ (b - 1) = (q : ℝ) := by
        dsimp [q]
        rw [Nat.cast_sub hk1, Nat.cast_mul, Nat.cast_pow]
        norm_num
      have hm1_cast :
          (doubleMacroNat b (k + 1) : ℝ) - 1 =
            ((doubleMacroNat b (k + 1) - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hm1]
        norm_num
      calc
        C₁ * Real.rpow (s : ℝ) ((b : ℝ) / (b - 1))
            ≤ ((s : ℝ) - 2 * (doubleMacroNat b k : ℝ) ^ (b - 1)) *
                (doubleMacroNat b (k + 1) : ℝ) +
                ((doubleMacroNat b (k + 1) : ℝ) - 1) := by
                  simpa [C₁] using hbound
        _ = (q : ℝ) * (doubleMacroNat b (k + 1) : ℝ) +
              ((doubleMacroNat b (k + 1) - 1 : ℕ) : ℝ) := by
                rw [hq_cast, hm1_cast]
        _ = ((q * doubleMacroNat b (k + 1) + (doubleMacroNat b (k + 1) - 1) : ℕ) : ℝ) := by
              rw [Nat.cast_add, Nat.cast_mul]
    exact Set.Subset.trans (hBall_mono hrad) hcover

theorem theorem6_expansion_upper_part (b : ℕ) (hb : 2 ≤ b) : ∃ C₂ B : ℝ, 0 < C₂ ∧ (∀ (s : ℕ), (s ≥ B) → let ub := Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)); ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ (A 1)))) := by
  refine ⟨(1 : ℝ), (b ^ (b - 1) : ℝ), zero_lt_one, ?_⟩
  intro s hs
  dsimp
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : 1 < (2 : ℕ)) hb
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb1
  have h1le : 1 ≤ b := le_of_lt hb1
  have hbm1_pos : 0 < b - 1 := by omega
  have hbm1_ne : b - 1 ≠ 0 := Nat.ne_of_gt hbm1_pos
  let k : ℕ := Nat.findGreatest (fun k => (doubleMacroNat b k) ^ (b - 1) ≤ s) s
  let m : ℕ := doubleMacroNat b (k + 1)
  intro hsub
  have h0 : (doubleMacroNat b 0) ^ (b - 1) ≤ s := by
    have hs_nat : b ^ (b - 1) ≤ s := by
      exact_mod_cast hs
    simpa [doubleMacroNat] using hs_nat
  have hk_spec : (doubleMacroNat b k) ^ (b - 1) ≤ s := by
    exact Nat.findGreatest_spec (m := 0) (n := s)
      (P := fun k => (doubleMacroNat b k) ^ (b - 1) ≤ s) (by simp) h0
  have hk_lt_x : k < doubleMacroNat b k := by
    have hk_lt_bk : k < b ^ k := Nat.lt_pow_self hb1
    have hk_bk_le : b ^ k ≤ doubleMacroNat b k := by
      dsimp [doubleMacroNat]
      exact Nat.pow_le_pow_right hb0 hk_lt_bk.le
    exact lt_of_lt_of_le hk_lt_bk hk_bk_le
  have hk_le_pow : doubleMacroNat b k ≤ (doubleMacroNat b k) ^ (b - 1) := by
    exact Nat.le_self_pow hbm1_ne _
  have hk_lt_s : k < s := by
    exact lt_of_lt_of_le hk_lt_x (le_trans hk_le_pow hk_spec)
  have hk1_le_s : k + 1 ≤ s := Nat.succ_le_of_lt hk_lt_s
  have hk_not : ¬ (doubleMacroNat b (k + 1)) ^ (b - 1) ≤ s := by
    exact Nat.findGreatest_is_greatest
      (P := fun k => (doubleMacroNat b k) ^ (b - 1) ≤ s)
      (n := s) (k := k + 1) (by simpa [k]) hk1_le_s
  have hk_max : s < (doubleMacroNat b (k + 1)) ^ (b - 1) := by
    exact lt_of_not_ge hk_not
  have hm_eq : m = (doubleMacroNat b k) ^ b := by
    dsimp [m, doubleMacroNat]
    rw [Nat.pow_succ, pow_mul]
  have hm_ge_b : b ≤ m := by
    dsimp [m, doubleMacroNat]
    exact Nat.le_self_pow (pow_ne_zero (k + 1) (Nat.ne_of_gt hb0)) _
  have hm_gt1 : 1 < m := lt_of_lt_of_le hb1 hm_ge_b
  have hsmall : 1 + s * m < doubleMacroNat b (k + 2) := by
    have hs_succ : s + 1 ≤ m ^ (b - 1) := Nat.succ_le_of_lt (by simpa [m] using hk_max)
    have hmul : (s + 1) * m ≤ m ^ (b - 1) * m := Nat.mul_le_mul_right m hs_succ
    have hlt : 1 + s * m < s * m + m := by
      omega
    have hlt2 : 1 + s * m < (s + 1) * m := by
      simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
    have hlt' : 1 + s * m < m ^ (b - 1) * m := lt_of_lt_of_le hlt2 hmul
    have hb_eq : b = (b - 1) + 1 := by omega
    have hpow : m ^ (b - 1) * m = m ^ b := by
      calc
        m ^ (b - 1) * m = m ^ ((b - 1) + 1) := by rw [← Nat.pow_succ]
        _ = m ^ b := by
          simpa using congrArg (fun n : ℕ => m ^ n) hb_eq.symm
    have hlt'' : 1 + s * m < m ^ b := by
      simpa [hpow] using hlt'
    have hm_succ : doubleMacroNat b (k + 2) = m ^ b := by
      dsimp [m, doubleMacroNat]
      rw [Nat.pow_succ, pow_mul]
    simpa [hm_succ] using hlt''
  have hnotmem : Multiset.replicate (1 + s * m) (0 : Fin 1) ∉ Ball s (DoublyMacroSet b ∪ A 1) := by
    simpa [m] using doubleMacro_full_witness_not_mem b (k + 1) s hb hsmall
  have hs_nonneg : 0 ≤ (s : ℝ) := by positivity
  have hb1R : (1 : ℝ) < b := by exact_mod_cast hb1
  have hden : (b : ℝ) - 1 ≠ 0 := by
    linarith
  have hsubR : (((b - 1 : ℕ) : ℝ)) = (b : ℝ) - (1 : ℝ) := by
    norm_num [Nat.cast_sub h1le]
  let x : ℕ := doubleMacroNat b k
  have hk_spec_x : x ^ (b - 1) ≤ s := by
    simpa [x] using hk_spec
  have hm_pow_eq : m ^ (b - 1) = (x ^ (b - 1)) ^ b := by
    rw [hm_eq]
    calc
      (doubleMacroNat b k ^ b) ^ (b - 1) = doubleMacroNat b k ^ (b * (b - 1)) := by
        rw [pow_mul]
      _ = doubleMacroNat b k ^ ((b - 1) * b) := by
        simp [Nat.mul_comm]
      _ = (doubleMacroNat b k ^ (b - 1)) ^ b := by
        rw [pow_mul]
      _ = (x ^ (b - 1)) ^ b := by
        simp [x]
  have hm_pow_le : m ^ (b - 1) ≤ s ^ b := by
    rw [hm_pow_eq]
    exact pow_le_pow_left' hk_spec_x b
  have hs_eq_nat : (((s : ℝ) ^ ((b : ℝ) / (b - 1))) ^ (b - 1)) = (s : ℝ) ^ b := by
    calc
      (((s : ℝ) ^ ((b : ℝ) / (b - 1))) ^ (b - 1))
          = (s : ℝ) ^ (((b : ℝ) / (b - 1)) * ((b - 1 : ℕ) : ℝ)) := by
              symm
              exact Real.rpow_mul_natCast hs_nonneg ((b : ℝ) / (b - 1)) (b - 1)
      _ = (s : ℝ) ^ (b : ℝ) := by
            have hfrac : ((b : ℝ) / (b - 1)) * ((b - 1 : ℕ) : ℝ) = (b : ℝ) := by
              rw [hsubR]
              field_simp [hden]
            rw [hfrac]
      _ = (s : ℝ) ^ b := by
            simpa [Real.rpow_natCast]
  have hm_pow_leR : (m : ℝ) ^ (b - 1) ≤ ((s : ℝ) ^ ((b : ℝ) / (b - 1))) ^ (b - 1) := by
    rw [hs_eq_nat]
    exact_mod_cast hm_pow_le
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hs_rpow_nonneg : 0 ≤ (s : ℝ) ^ ((b : ℝ) / (b - 1)) := by
    exact Real.rpow_nonneg hs_nonneg _
  have hz_pos : 0 < ((b - 1 : ℕ) : ℝ) := by
    exact_mod_cast hbm1_pos
  have hm_le : (m : ℝ) ≤ (s : ℝ) ^ ((b : ℝ) / (b - 1)) := by
    have hm_pow_leR' : (m : ℝ) ^ ((b - 1 : ℕ) : ℝ) ≤
        ((s : ℝ) ^ ((b : ℝ) / (b - 1))) ^ ((b - 1 : ℕ) : ℝ) := by
      simpa [Real.rpow_natCast] using hm_pow_leR
    exact (Real.rpow_le_rpow_iff hm_nonneg hs_rpow_nonneg hz_pos).1 hm_pow_leR'
  have hmul1 : (s * m : ℝ) ≤ (s : ℝ) * ((s : ℝ) ^ ((b : ℝ) / (b - 1))) := by
    exact mul_le_mul_of_nonneg_left hm_le hs_nonneg
  have hmul2 : (s : ℝ) * ((s : ℝ) ^ ((b : ℝ) / (b - 1))) ≤
      (s : ℝ) ^ (1 + (b : ℝ) / (b - 1)) := by
    simpa [Real.rpow_natCast] using
      (Real.le_rpow_add hs_nonneg (1 : ℝ) ((b : ℝ) / (b - 1)))
  have hexp : (1 : ℝ) + (b : ℝ) / (b - 1) = ((2 * (b : ℝ) - 1) / (b - 1)) := by
    field_simp [hden]
    ring
  have hle_ub : (s * m : ℝ) ≤ (s : ℝ) ^ ((2 * (b : ℝ) - 1) / (b - 1)) := by
    exact le_trans hmul1 (by simpa [hexp] using hmul2)
  have hfloor : s * m ≤ Int.toNat (Int.floor ((s : ℝ) ^ ((2 * (b : ℝ) - 1) / (b - 1)))) := by
    have hle_ub' : ((s * m : ℕ) : ℝ) ≤ (s : ℝ) ^ ((2 * (b : ℝ) - 1) / (b - 1)) := by
      simpa [Nat.cast_mul] using hle_ub
    simpa [Int.floor_toNat] using (Nat.le_floor hle_ub')
  have hwA : Multiset.replicate (1 + s * m) (0 : Fin 1) ∈ Ball (1 + Int.toNat <| Int.floor <| (1 : ℝ) * ((s : ℝ) ^ ((2 * (b : ℝ) - 1) / (b - 1)))) (A 1) := by
    apply (ball_A1_iff_card_le _ _).2
    simp
    simpa using hfloor
  exact hnotmem (hsub hwA)

theorem theorem6_expansion_part (b : ℕ) (hb : 2 ≤ b) : ∃ C₁ C₂ B : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ (∀ (s : ℕ), (s ≥ B) → let lb := Real.rpow s ((b : ℝ) / (b - 1)); (Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ (A 1))) ∧ let ub := Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1)); ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ (A 1)))) := by
  rcases theorem6_expansion_lower_part b hb with ⟨C₁, B₁, hC₁pos, hlower⟩
  rcases theorem6_expansion_upper_part b hb with ⟨C₂, B₂, hC₂pos, hupper⟩
  refine ⟨C₁, C₂, max B₁ B₂, hC₁pos, hC₂pos, ?_⟩
  intro s hs
  have hs1 : s ≥ B₁ := le_trans (le_max_left B₁ B₂) hs
  have hs2 : s ≥ B₂ := le_trans (le_max_right B₁ B₂) hs
  constructor
  · exact hlower s hs1
  · exact hupper s hs2

theorem theorem6 (b : ℕ) (hb : 2 ≤ b) : let M := DoublyMacroSet b
  (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ b ^ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ (Ball x (A 1))).ncard
      ∧ (M ∩ (Ball x (A 1))).ncard ≤ d2 * (Real.log (Real.log x))) ∧
  (∃ C₁ C₂ B : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ B) →
      let lb := Real.rpow s ((b : ℝ) / (b - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * lb) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
        let ub := Real.rpow s ((2 * (b : ℝ) - 1) / (b - 1))
        ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * ub) (A 1) ⊆ Ball s (M ∪ (A 1))))) := by
  dsimp
  exact ⟨theorem6_density_part b hb, theorem6_expansion_part b hb⟩

