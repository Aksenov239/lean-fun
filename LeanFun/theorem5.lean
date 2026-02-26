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

theorem Ball_mono_R {n : ℕ} {R R' : ℕ} {X : Set (FreeAbelianMonoid n)} (h : R ≤ R') : Ball R X ⊆ Ball R' X := by
  intro m hm
  rcases hm with ⟨l, hl, hX, hsum⟩
  refine ⟨l, le_trans hl h, hX, hsum⟩

theorem Ball_mono_X {n : ℕ} {R : ℕ} {X Y : Set (FreeAbelianMonoid n)} (h : X ⊆ Y) : Ball R X ⊆ Ball R Y := by
  intro m hm
  rcases hm with ⟨l, hl, hX, hsum⟩
  refine ⟨l, hl, ?_, hsum⟩
  intro x hx
  exact h (hX x hx)

theorem alpha_le_two (b : ℕ) (hb : 2 ≤ b) : ((b : ℝ) / (b - 1) : ℝ) ≤ 2 := by
  have hb1nat : 1 < b := by
    omega
  have hb1R : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb1nat
  have hpos : (0 : ℝ) < (b : ℝ) - 1 := by
    exact sub_pos.mpr hb1R
  have hmul : (b : ℝ) ≤ (2 : ℝ) * ((b : ℝ) - 1) := by
    have hbR : (2 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast hb
    nlinarith
  -- rewrite by multiplying both sides by the positive denominator
  -- `div_le_iff₀` uses the assumption that the denominator is positive
  exact (div_le_iff₀ hpos).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)


theorem ball_A1_exists_replicate {R : ℕ} {m : FreeAbelianMonoid 1} : m ∈ Ball R (A 1) → ∃ k : ℕ, k ≤ R ∧ m = Multiset.replicate k (0 : Fin 1) := by
  intro hm
  rcases hm with ⟨l, hlR, hlmem, hsum⟩
  refine ⟨l.length, hlR, ?_⟩
  -- show that the sum of a list of elements of `A 1` is a replicate of `0`
  have hrep : ∀ l : List (FreeAbelianMonoid 1),
      (∀ x, x ∈ l → x ∈ A 1) → l.sum = Multiset.replicate l.length (0 : Fin 1) := by
    intro l
    induction l with
    | nil =>
        intro _
        simp
    | cons a t ih =>
        intro h
        have ha : a ∈ A 1 := h a (by simp)
        have ht : ∀ x, x ∈ t → x ∈ A 1 := by
          intro x hx
          exact h x (by simp [hx])
        rcases ha with ⟨i, rfl⟩
        have hi : i = (0 : Fin 1) := by
          exact Subsingleton.elim i 0
        subst hi
        have htsum : t.sum = Multiset.replicate t.length (0 : Fin 1) := ih ht
        -- now compute the sum
        simp [List.sum_cons, List.length_cons, htsum, Multiset.singleton_add, Multiset.replicate_succ]
  have hsum' : l.sum = Multiset.replicate l.length (0 : Fin 1) := hrep l hlmem
  exact hsum.symm.trans hsum'

theorem div_mul_sq_five_Ppow_eq_cast_pow (b P : ℕ) (hb1 : 1 ≤ b) :
  ((P : ℝ) / 25) * ((5 * P ^ (b - 1) : ℝ) ^ 2) = ((P ^ (b - 1 + b) : ℕ) : ℝ) := by
  
  have h25 : (25 : ℝ) ≠ 0 := by
    norm_num
  have hb : b - 1 + 1 = b := Nat.sub_add_cancel hb1
  calc
    ((P : ℝ) / 25) * ((5 * P ^ (b - 1) : ℝ) ^ 2)
        = ((P : ℝ) / 25) * (((5 : ℝ) * (P : ℝ) ^ (b - 1)) ^ 2) := by
            simp only [Nat.cast_mul, Nat.cast_pow]
    _ = ((P : ℝ) / 25) * ((5 : ℝ) ^ 2 * ((P : ℝ) ^ (b - 1)) ^ 2) := by
            simp only [mul_pow]
    _ = ((P : ℝ) / 25) * (25 * ((P : ℝ) ^ (b - 1)) ^ 2) := by
            norm_num
    _ = (P : ℝ) * ((P : ℝ) ^ (b - 1)) ^ 2 := by
            -- cancel the factor 25
            rw [← mul_assoc ((P : ℝ) / 25) (25 : ℝ) (((P : ℝ) ^ (b - 1)) ^ 2)]
            simp only [div_mul_cancel₀ (P : ℝ) h25]
    _ = ((P ^ (b - 1 + b) : ℕ) : ℝ) := by
            -- turn RHS into a real power
            simp only [Nat.cast_pow]
            -- Expand the square and combine exponents
            rw [pow_two]
            -- reassociate: P * (x * x) = (P * x) * x
            rw [← mul_assoc (P : ℝ) ((P : ℝ) ^ (b - 1)) ((P : ℝ) ^ (b - 1))]
            -- commute the first two factors so we can use `pow_succ`
            rw [mul_comm (P : ℝ) ((P : ℝ) ^ (b - 1))]
            -- (P^(b-1)) * P = P^(b-1+1)
            rw [← pow_succ (P : ℝ) (b - 1)]
            -- rewrite (b-1+1) as b
            rw [hb]
            -- now combine the remaining product of powers
            rw [mul_comm ((P : ℝ) ^ b) ((P : ℝ) ^ (b - 1))]
            rw [← pow_add (P : ℝ) (b - 1) b]


theorem exists_pow_pow_ge (b : ℕ) (hb : 2 ≤ b) (x : ℝ) : ∃ j : ℕ, x ≤ (b : ℝ) ^ (b ^ j) := by
  have hb1_nat : 1 < b := by
    omega
  have hb1_real : (1 : ℝ) < (b : ℝ) := by
    exact_mod_cast hb1_nat
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x := x) (y := (b : ℝ)) hb1_real
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (x := n) (y := b) hb1_nat
  refine ⟨j, ?_⟩
  have hxle : x ≤ (b : ℝ) ^ n := le_of_lt hn
  have hnj : n ≤ b ^ j := Nat.le_of_lt hj
  have hb1_le : (1 : ℝ) ≤ (b : ℝ) := le_of_lt hb1_real
  have hpow : (b : ℝ) ^ n ≤ (b : ℝ) ^ (b ^ j) := by
    exact pow_le_pow_right₀ hb1_le hnj
  exact le_trans hxle hpow

theorem floor_toNat_le_of_le_nat (x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hxn : x ≤ n) : Int.toNat (Int.floor x) ≤ n := by
  -- Rewrite `Int.toNat (Int.floor x)` as the natural floor and use its monotonicity.
  simpa [Int.floor_toNat] using (Nat.floor_le_of_le (a := x) (n := n) hxn)


theorem pow_pow_eq_pow_pow_succ (b j : ℕ) : (b ^ (b ^ j)) ^ b = b ^ (b ^ (j + 1)) := by
  calc
    (b ^ (b ^ j)) ^ b = b ^ (b ^ j * b) := by
      simpa using (pow_mul b (b ^ j) b).symm
    _ = b ^ (b ^ (j + 1)) := by
      refine congrArg (fun n : ℕ => b ^ n) ?_
      simpa using (pow_succ b j).symm


theorem replicate_pow_pow_mem_DoublyMacroSet (b j : ℕ) : (Multiset.replicate (b ^ (b ^ j)) (0 : Fin 1) : FreeAbelianMonoid 1) ∈ DoublyMacroSet b := by
  unfold DoublyMacroSet
  refine ⟨(0 : Fin 1), j, ?_⟩
  rfl


theorem doublyMacro_cover_Ppowb (b j : ℕ) (hb : 2 ≤ b) :
  let P : ℕ := b ^ (b ^ j)
  let t : ℕ := P ^ (b - 1) + P
  let M : Set (FreeAbelianMonoid 1) := DoublyMacroSet b
  Ball (P ^ b) (A 1) ⊆ Ball t (M ∪ A 1) := by
  classical
  dsimp
  set P : ℕ := b ^ (b ^ j) with hP
  set t : ℕ := P ^ (b - 1) + P with ht
  set M : Set (FreeAbelianMonoid 1) := DoublyMacroSet b with hM
  intro m hm
  rcases ball_A1_exists_replicate (R := P ^ b) (m := m) hm with ⟨k, hk, rfl⟩
  let q : ℕ := k / P
  let r : ℕ := k % P
  let big : FreeAbelianMonoid 1 := Multiset.replicate P (0 : Fin 1)
  let small : FreeAbelianMonoid 1 := ({(0 : Fin 1)} : Multiset (Fin 1))
  let l : List (FreeAbelianMonoid 1) := List.replicate q big ++ List.replicate r small

  have hb0 : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  have Ppos : 0 < P := by
    simpa [hP] using (pow_pos hb0 (b ^ j))

  have hr_lt : r < P := by
    have : k % P < P := Nat.mod_lt k Ppos
    simpa [r] using this
  have hr_le : r ≤ P := le_of_lt hr_lt

  have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
  have hpow : P ^ b = P ^ (b - 1) * P := by
    have hb_sub : b - 1 + 1 = b := Nat.sub_add_cancel hb1
    -- `pow_succ` gives `P^(b-1+1) = P^(b-1)*P`; rewrite `(b-1+1)` to `b`.
    simpa [hb_sub] using (pow_succ P (b - 1))

  have hk_mul : k ≤ P * P ^ (b - 1) := by
    have hk1 : k ≤ P ^ (b - 1) * P := by
      calc
        k ≤ P ^ b := hk
        _ = P ^ (b - 1) * P := hpow
    exact hk1.trans (le_of_eq (Nat.mul_comm (P ^ (b - 1)) P))

  have hq_le : q ≤ P ^ (b - 1) := by
    have : k / P ≤ P ^ (b - 1) :=
      Nat.div_le_of_le_mul' (m := k) (k := P) (n := P ^ (b - 1)) hk_mul
    simpa [q] using this

  have hbig : big ∈ M := by
    rw [hM]
    simpa [big, hP] using replicate_pow_pow_mem_DoublyMacroSet b j

  have hsmall : small ∈ A 1 := by
    refine ⟨(0 : Fin 1), ?_⟩
    simp [A, small]

  have hlen' : l.length ≤ P ^ (b - 1) + P := by
    have : q + r ≤ P ^ (b - 1) + P := Nat.add_le_add hq_le hr_le
    simpa [l, List.length_append, List.length_replicate] using this

  have hlen : l.length ≤ t := by
    simpa [ht] using hlen'

  have hmem : ∀ x, x ∈ l → x ∈ M ∪ A 1 := by
    intro x hx
    rcases (List.mem_append.1 hx) with hx | hx
    · have hxEq : x = big := by
        exact (List.mem_replicate.1 hx).2
      refine Or.inl ?_
      simpa [hxEq] using hbig
    · have hxEq : x = small := by
        exact (List.mem_replicate.1 hx).2
      refine Or.inr ?_
      simpa [hxEq] using hsmall

  have hkqr : q * P + r = k := by
    simpa [q, r, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using (Nat.div_add_mod k P)

  have hsum' : l.sum = Multiset.replicate (q * P + r) (0 : Fin 1) := by
    calc
      l.sum = Multiset.replicate (q * P) (0 : Fin 1) + Multiset.replicate r (0 : Fin 1) := by
        simp [l, big, small, List.sum_append, List.sum_replicate, Multiset.nsmul_replicate,
          Multiset.nsmul_singleton]
      _ = Multiset.replicate (q * P + r) (0 : Fin 1) := by
        simpa using (Multiset.replicate_add (q * P) r (0 : Fin 1)).symm

  have hsum : l.sum = Multiset.replicate k (0 : Fin 1) := by
    simpa [hkqr] using hsum'

  exact ⟨l, hlen, hmem, hsum⟩

theorem doublyMacro_cover_scaled (b j : ℕ) (hb : 2 ≤ b) :
  let P : ℕ := b ^ (b ^ j)
  let t : ℕ := P ^ (b - 1) + P
  let L : ℕ := P ^ b
  let s : ℕ := 2 * t + 1
  let M : Set (FreeAbelianMonoid 1) := DoublyMacroSet b
  Ball ((t + 1) * L + 1) (A 1) ⊆ Ball s (M ∪ A 1) := by
  classical
  dsimp
  set P : ℕ := b ^ (b ^ j) with hP
  set t : ℕ := P ^ (b - 1) + P with ht
  set L : ℕ := P ^ b with hL
  set s : ℕ := 2 * t + 1 with hs
  set M : Set (FreeAbelianMonoid 1) := DoublyMacroSet b with hM
  have hrem : Ball L (A 1) ⊆ Ball t (M ∪ A 1) := by
    simpa [hP, ht, hL, hM] using (doublyMacro_cover_Ppowb (b := b) (j := j) hb)
  intro m hm
  rcases ball_A1_exists_replicate (R := (t + 1) * L + 1) (m := m) hm with ⟨k, hk, rfl⟩
  set q : ℕ := k / L with hq
  set r : ℕ := k % L with hr
  have hLpos : 0 < L := by
    have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hb
    have hPpos : 0 < P := by
      simpa [hP] using pow_pos hbpos (b ^ j)
    have : 0 < P ^ b := pow_pos hPpos b
    simpa [hL] using this
  have hrLt : r < L := by
    have : k % L < L := Nat.mod_lt k hLpos
    simpa [hr] using this
  have hrle : r ≤ L := le_of_lt hrLt
  have hLgt : 1 < L := by
    have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hbne0 : b ≠ 0 := ne_of_gt (lt_trans (by decide : (0 : ℕ) < 1) hb1)
    have hPgt : 1 < P := by
      have hexp : b ^ j ≠ 0 := by
        exact pow_ne_zero j (ne_of_gt (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hb))
      have : 1 < b ^ (b ^ j) := one_lt_pow' hb1 hexp
      simpa [hP] using this
    have : 1 < P ^ b := one_lt_pow' hPgt hbne0
    simpa [hL] using this
  have hklt : k < (t + 2) * L := by
    have h1 : (t + 1) * L + 1 < (t + 2) * L := by
      have : (t + 1) * L + 1 < (t + 1) * L + L := Nat.add_lt_add_left hLgt ((t + 1) * L)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.succ_mul] using this
    exact lt_of_le_of_lt hk h1
  have hqLt : q < t + 2 := by
    have : k / L < t + 2 := (Nat.div_lt_iff_lt_mul hLpos).2 (by
      simpa [Nat.mul_comm] using hklt)
    simpa [hq] using this
  have hqle : q ≤ t + 1 := by
    have : q < Nat.succ (t + 1) := by
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hqLt
    exact Nat.lt_succ_iff.mp this
  have hrem_r : (Multiset.replicate r (0 : Fin 1) : FreeAbelianMonoid 1) ∈ Ball t (M ∪ A 1) := by
    have hrBallr : (Multiset.replicate r (0 : Fin 1) : FreeAbelianMonoid 1) ∈ Ball r (A 1) := by
      refine ⟨List.replicate r ({(0 : Fin 1)} : Multiset (Fin 1)), ?_⟩
      refine ⟨?_, ?_⟩
      · simp
      refine ⟨?_, ?_⟩
      · intro x hx
        have hx' : x ∈ ([({(0 : Fin 1)} : Multiset (Fin 1))]) :=
          (List.replicate_subset_singleton r ({(0 : Fin 1)} : Multiset (Fin 1))) hx
        have hxg : x = ({(0 : Fin 1)} : Multiset (Fin 1)) := by
          simpa using hx'
        subst hxg
        simpa [A]
      · simpa [List.sum_replicate, Multiset.nsmul_singleton]
    have hrBallL : (Multiset.replicate r (0 : Fin 1) : FreeAbelianMonoid 1) ∈ Ball L (A 1) :=
      (Ball_mono_R (X := A 1) (h := hrle)) hrBallr
    exact hrem hrBallL
  rcases hrem_r with ⟨lrem, hlrem_len, hlrem_mem, hlrem_sum⟩
  -- macro coin element
  set coin : FreeAbelianMonoid 1 := Multiset.replicate L (0 : Fin 1) with hcoin
  have hcoinM : coin ∈ M := by
    have hLpow : L = b ^ (b ^ (j + 1)) := by
      calc
        L = P ^ b := by simpa [hL]
        _ = (b ^ (b ^ j)) ^ b := by simpa [hP]
        _ = b ^ ((b ^ j) * b) := by
          simpa using (pow_mul b (b ^ j) b).symm
        _ = b ^ (b ^ (j + 1)) := by
          simp [pow_succ, Nat.mul_assoc]
    have : (Multiset.replicate (b ^ (b ^ (j + 1))) (0 : Fin 1) : FreeAbelianMonoid 1) ∈ DoublyMacroSet b :=
      replicate_pow_pow_mem_DoublyMacroSet b (j + 1)
    simpa [hcoin, hM, hLpow] using this
  refine ⟨(List.replicate q coin) ++ lrem, ?_⟩
  refine ⟨?_, ?_⟩
  · -- length
    have hlen_qt : (List.replicate q coin ++ lrem).length ≤ q + t := by
      simpa [List.length_append] using (Nat.add_le_add_left hlrem_len q)
    have hqt : q + t ≤ s := by
      have h1 : q + t ≤ (t + 1) + t := Nat.add_le_add_right hqle t
      have h2 : (t + 1) + t = 2 * t + 1 := by
        simp [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have : q + t ≤ 2 * t + 1 := by simpa [h2] using h1
      simpa [hs] using this
    exact le_trans hlen_qt hqt
  refine ⟨?_, ?_⟩
  · -- membership
    intro x hx
    have hx' : x ∈ List.replicate q coin ∨ x ∈ lrem := by
      simpa [List.mem_append] using hx
    rcases hx' with hxrep | hxrem
    · have hx'' : x = coin := by
        have : x ∈ [coin] := (List.replicate_subset_singleton q coin) hxrep
        simpa using this
      subst hx''
      exact Or.inl hcoinM
    · exact hlrem_mem x hxrem
  · -- sum
    have hsumrep : (List.replicate q coin).sum = q • coin := by
      simpa using (List.sum_replicate q coin)
    have hqcoin : q • coin = (Multiset.replicate (q * L) (0 : Fin 1) : FreeAbelianMonoid 1) := by
      simp [hcoin, Multiset.nsmul_replicate, Nat.mul_assoc]
    have hk_eq : q * L + r = k := by
      have := Nat.div_add_mod k L
      simpa [hq, hr, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using this
    calc
      (List.replicate q coin ++ lrem).sum
          = (List.replicate q coin).sum + lrem.sum := by
              simp [List.sum_append]
      _ = (q • coin) + lrem.sum := by
              simp [hsumrep]
      _ = (Multiset.replicate (q * L) (0 : Fin 1) : FreeAbelianMonoid 1) + (Multiset.replicate r (0 : Fin 1) : FreeAbelianMonoid 1) := by
              simp [hqcoin, hlrem_sum]
      _ = (Multiset.replicate (q * L + r) (0 : Fin 1) : FreeAbelianMonoid 1) := by
              simpa using (Multiset.replicate_add (q * L) r (0 : Fin 1)).symm
      _ = (Multiset.replicate k (0 : Fin 1) : FreeAbelianMonoid 1) := by
              simpa [hk_eq]


theorem rpow_le_sq_of_alpha_le_two (b : ℕ) (hb : 2 ≤ b) (s : ℕ) (hs : 1 ≤ s) : Real.rpow s ((b : ℝ) / (b - 1)) ≤ (s : ℝ) ^ (2 : ℝ) := by
  -- Let α = (b : ℝ) / (b - 1)
  have hs' : (1 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hs
  -- monotonicity of x ↦ x^y for x ≥ 1 in the exponent
  simpa using
    (Real.rpow_le_rpow_of_exponent_le (x := (s : ℝ)) hs' (alpha_le_two b hb))


theorem scaled_Ppow_bm1_add_b_le_tL (b P : ℕ) :
  let t : ℕ := P ^ (b - 1) + P
  let L : ℕ := P ^ b
  P ^ (b - 1 + b) ≤ (t + 1) * L := by
  -- Expand the `let` bindings and rewrite the power on the left.
  simp only [pow_add]
  -- It suffices to bound the left factor and then multiply by `P ^ b`.
  apply Nat.mul_le_mul_right (P ^ b)
  -- `P^(b-1) ≤ P^(b-1) + P + 1` is immediate since we add nonnegative terms.
  calc
    P ^ (b - 1) ≤ P ^ (b - 1) + P := by
      simpa using (self_le_add_right (P ^ (b - 1)) P)
    _ ≤ P ^ (b - 1) + P + 1 := by
      simpa using (self_le_add_right (P ^ (b - 1) + P) 1)

theorem scaled_s_le_five_Ppow (b P : ℕ) (hb : 2 ≤ b) (hP : 1 ≤ P) :
  let t : ℕ := P ^ (b - 1) + P
  let s : ℕ := 2 * t + 1
  s ≤ 5 * P ^ (b - 1) := by
  dsimp
  have hb' : b - 1 ≠ 0 := by
    omega
  have hP_le : P ≤ P ^ (b - 1) := by
    exact le_self_pow hP hb'
  have hpow1 : 1 ≤ P ^ (b - 1) := by
    exact one_le_pow_of_one_le' hP (b - 1)
  have ht : P ^ (b - 1) + P ≤ P ^ (b - 1) + P ^ (b - 1) := by
    exact Nat.add_le_add_left hP_le (P ^ (b - 1))
  have hs1 : 2 * (P ^ (b - 1) + P) + 1 ≤ 2 * (P ^ (b - 1) + P ^ (b - 1)) + 1 := by
    have hmul : 2 * (P ^ (b - 1) + P) ≤ 2 * (P ^ (b - 1) + P ^ (b - 1)) := by
      exact Nat.mul_le_mul_left 2 ht
    exact Nat.add_le_add_right hmul 1
  have hs2 : 2 * (P ^ (b - 1) + P ^ (b - 1)) + 1 ≤ 5 * P ^ (b - 1) := by
    have hleft : 2 * (P ^ (b - 1) + P ^ (b - 1)) + 1 = 4 * P ^ (b - 1) + 1 := by
      ring
    have h4 : 4 * P ^ (b - 1) + 1 ≤ 5 * P ^ (b - 1) := by
      have haux : 4 * P ^ (b - 1) + 1 ≤ 4 * P ^ (b - 1) + P ^ (b - 1) := by
        exact Nat.add_le_add_left hpow1 (4 * P ^ (b - 1))
      have hr : 4 * P ^ (b - 1) + P ^ (b - 1) = 5 * P ^ (b - 1) := by
        ring
      exact le_trans haux (le_of_eq hr)
    -- rewrite using hleft
    simpa [hleft] using h4
  exact le_trans hs1 hs2

theorem scaled_C2_mul_s_sq_le_tL (b P : ℕ) (hb : 2 ≤ b) (hP : 1 ≤ P)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂) (hC₂P : 25 * C₂ ≤ (P : ℝ)) :
  let t : ℕ := P ^ (b - 1) + P
  let L : ℕ := P ^ b
  let s : ℕ := 2 * t + 1
  C₂ * (s : ℝ) ^ 2 ≤ (t + 1) * L := by
  classical
  dsimp
  have hsNat : 2 * (P ^ (b - 1) + P) + 1 ≤ 5 * P ^ (b - 1) := by
    simpa using (scaled_s_le_five_Ppow b P hb hP)
  have hsReal : ((2 * (P ^ (b - 1) + P) + 1 : ℕ) : ℝ) ≤ (5 * P ^ (b - 1) : ℝ) := by
    exact_mod_cast hsNat
  have hs0 : (0 : ℝ) ≤ ((2 * (P ^ (b - 1) + P) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_le (2 * (P ^ (b - 1) + P) + 1))
  have hsSq : (((2 * (P ^ (b - 1) + P) + 1 : ℕ) : ℝ) ^ 2) ≤ ((5 * P ^ (b - 1) : ℝ) ^ 2) := by
    simpa using (pow_le_pow_left₀ hs0 hsReal 2)
  have hmul1 :
      C₂ * (((2 * (P ^ (b - 1) + P) + 1 : ℕ) : ℝ) ^ 2) ≤ C₂ * ((5 * P ^ (b - 1) : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsSq hC₂
  have hC2le : C₂ ≤ (P : ℝ) / 25 := by
    have h25pos : (0 : ℝ) < 25 := by
      norm_num
    have hC2mul : C₂ * 25 ≤ (P : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hC₂P
    exact (le_div_iff₀ h25pos).2 hC2mul
  have hsSq0 : 0 ≤ ((5 * P ^ (b - 1) : ℝ) ^ 2) := by
    exact sq_nonneg (5 * P ^ (b - 1) : ℝ)
  have hmul2 :
      C₂ * ((5 * P ^ (b - 1) : ℝ) ^ 2) ≤ ((P : ℝ) / 25) * ((5 * P ^ (b - 1) : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_right hC2le hsSq0
  have hmul :
      C₂ * (((2 * (P ^ (b - 1) + P) + 1 : ℕ) : ℝ) ^ 2) ≤
        ((P : ℝ) / 25) * ((5 * P ^ (b - 1) : ℝ) ^ 2) := by
    exact le_trans hmul1 hmul2
  have hb1 : 1 ≤ b := by
    exact le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hdiv :
      ((P : ℝ) / 25) * ((5 * P ^ (b - 1) : ℝ) ^ 2) = ((P ^ (b - 1 + b) : ℕ) : ℝ) := by
    simpa using (div_mul_sq_five_Ppow_eq_cast_pow b P hb1)
  have hmul' :
      C₂ * (((2 * (P ^ (b - 1) + P) + 1 : ℕ) : ℝ) ^ 2) ≤ ((P ^ (b - 1 + b) : ℕ) : ℝ) := by
    simpa [hdiv] using hmul
  have hPowNat : P ^ (b - 1 + b) ≤ (P ^ (b - 1) + P + 1) * P ^ b := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (scaled_Ppow_bm1_add_b_le_tL b P)
  have hPowReal' :
      ((P ^ (b - 1 + b) : ℕ) : ℝ) ≤ (((P ^ (b - 1) + P + 1) * P ^ b : ℕ) : ℝ) := by
    exact_mod_cast hPowNat
  have hPowReal :
      ((P ^ (b - 1 + b) : ℕ) : ℝ) ≤ (↑(P ^ (b - 1) + P) + 1) * (↑(P ^ b) : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_add, add_assoc, add_left_comm, add_comm] using hPowReal'
  exact le_trans hmul' hPowReal

theorem theorem5_upper_bound_neg (b : ℕ) (hb : 2 ≤ b) :
  let M := DoublyMacroSet b
  ¬ (∃ C₂ B : ℝ,
      0 < C₂ ∧
      (∀ (s : ℕ), (s ≥ B) →
      let rs := Real.rpow s ((b : ℝ) / (b - 1))
      ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆ Ball s (M ∪ (A 1)))
    ) := by
  classical
  dsimp
  rintro ⟨C₂, B, hC₂pos, hbad⟩
  -- Choose a large scale parameter
  let x : ℝ := max B (max (25 * C₂) 1)
  obtain ⟨j, hj⟩ := exists_pow_pow_ge b hb x
  let P : ℕ := b ^ (b ^ j)
  have hxP : x ≤ (P : ℝ) := by
    simpa [P] using hj
  -- Define the scaled parameters
  let t : ℕ := P ^ (b - 1) + P
  let L : ℕ := P ^ b
  let s : ℕ := 2 * t + 1

  have hs_pos : 1 ≤ s := by
    dsimp [s]
    omega

  have hcover : Ball ((t + 1) * L + 1) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) := by
    -- Unfold the `let`s from `doublyMacro_cover_scaled`
    simpa [P, t, L, s] using (doublyMacro_cover_scaled b j hb)

  -- Show `s` is large enough to trigger the bad hypothesis
  have hBx : B ≤ x := by
    dsimp [x]
    exact le_max_left _ _
  have hBs : B ≤ (s : ℝ) := by
    have hBP : B ≤ (P : ℝ) := le_trans hBx hxP
    have hPt : P ≤ t := by
      dsimp [t]
      omega
    have ht_s : t ≤ s := by
      dsimp [s]
      omega
    have hPs_nat : P ≤ s := le_trans hPt ht_s
    have hPs : (P : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hPs_nat
    exact le_trans hBP hPs

  -- Set `rs` and bound it by `s^2`
  let rs : ℝ := Real.rpow s ((b : ℝ) / (b - 1))
  have hrs_le : rs ≤ (s : ℝ) ^ (2 : ℝ) := by
    dsimp [rs]
    simpa using (rpow_le_sq_of_alpha_le_two b hb s hs_pos)

  -- Get the `tL` bound for `C₂ * (s:ℝ)^2`
  have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hP1 : 1 ≤ P := by
    dsimp [P]
    exact one_le_pow_of_one_le' hb1 _

  have hC₂nonneg : 0 ≤ C₂ := le_of_lt hC₂pos
  have hC₂P : 25 * C₂ ≤ (P : ℝ) := by
    have h25le : 25 * C₂ ≤ x := by
      dsimp [x]
      have h₁ : 25 * C₂ ≤ max (25 * C₂) 1 := le_max_left _ _
      have h₂ : max (25 * C₂) 1 ≤ max B (max (25 * C₂) 1) := le_max_right _ _
      exact le_trans h₁ h₂
    exact le_trans h25le hxP

  have hC₂ssq_le : C₂ * ((s : ℝ) ^ (2 : ℝ)) ≤ ((t + 1) * L : ℝ) := by
    -- Apply the provided scaled inequality (and normalize casts)
    have h' : C₂ * ((s : ℝ) ^ (2 : ℝ)) ≤ (t + 1) * L := by
      simpa [t, L, s] using (scaled_C2_mul_s_sq_le_tL b P hb hP1 C₂ hC₂nonneg hC₂P)
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h'

  have hC₂rs_le : C₂ * rs ≤ ((t + 1) * L : ℝ) := by
    have hmul : C₂ * rs ≤ C₂ * ((s : ℝ) ^ (2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hrs_le hC₂nonneg
    exact le_trans hmul hC₂ssq_le

  have hrs_nonneg : 0 ≤ rs := by
    dsimp [rs]
    exact Real.rpow_nonneg (by positivity) _

  have hC₂rs_nonneg : 0 ≤ C₂ * rs := by
    exact mul_nonneg hC₂nonneg hrs_nonneg

  -- Convert to a floor / Nat inequality
  have hfloor : Int.toNat (Int.floor (C₂ * rs)) ≤ (t + 1) * L :=
    floor_toNat_le_of_le_nat (C₂ * rs) ((t + 1) * L) hC₂rs_nonneg (by
      -- `hC₂rs_le` has target casted to `ℝ`
      simpa using hC₂rs_le)

  have hR : (1 + Int.toNat (Int.floor (C₂ * rs))) ≤ (t + 1) * L + 1 := by
    have := Nat.add_le_add_left hfloor 1
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

  have hmono : Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆ Ball ((t + 1) * L + 1) (A 1) :=
    Ball_mono_R hR

  have hgood : Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆ Ball s (DoublyMacroSet b ∪ A 1) :=
    Set.Subset.trans hmono hcover

  -- Contradiction with the assumed badness
  exact (hbad s hBs) hgood


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
