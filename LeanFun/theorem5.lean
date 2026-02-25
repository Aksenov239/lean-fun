import LeanFun.Definitions

open abelian

def DoublyMacroSet (b : ℕ) : Set (FreeAbelianMonoid 1) :=
  { m | ∃ i : Fin 1, ∃ j : ℕ, 0 ≤ j ∧ m = Multiset.replicate (b ^ (b ^ j)) i }

theorem b2_pow_eq_sq (s : ℕ) : ((s : ℝ) ^ ((2 : ℝ) / (2 - 1))) = (s : ℝ) ^ 2 := by
  -- simplify the exponent
  norm_num

theorem b2_rs_eq_sq (s : ℕ) : Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1)) = (s : ℝ) ^ 2 := by
  simpa using (b2_pow_eq_sq s)


theorem ball_A1_iff_card_le {R : ℕ} (m : FreeAbelianMonoid 1) : m ∈ Ball R (A 1) ↔ m.card ≤ R := by
  constructor
  · intro hm
    rcases hm with ⟨l, hlR, hlA, hsum⟩

    have hsum_card :
        ∀ l : List (FreeAbelianMonoid 1),
          (∀ x, x ∈ l → x ∈ A 1) → (l.sum).card = l.length := by
      intro l
      induction l with
      | nil =>
          intro _
          simp
      | cons a t ih =>
          intro hA
          have haA : a ∈ A 1 := hA a (by simp)
          rcases (by simpa [A] using haA) with ⟨i, rfl⟩
          have htA : ∀ x, x ∈ t → x ∈ A 1 := by
            intro x hx
            exact hA x (by simp [hx])
          have ih' : (t.sum).card = t.length := ih htA
          simpa [List.sum_cons, Multiset.card_add, ih', Nat.one_add]

    have hcardm : m.card = l.length := by
      simpa [hsum] using (hsum_card l hlA)

    simpa [hcardm] using hlR

  · intro hmR
    refine ⟨List.replicate m.card ({(0 : Fin 1)} : Multiset (Fin 1)), ?_, ?_, ?_⟩
    · simpa using hmR
    · intro x hx
      have hx' : x ∈ [({(0 : Fin 1)} : Multiset (Fin 1))] :=
        (List.replicate_subset_singleton (n := m.card)
            (a := ({(0 : Fin 1)} : Multiset (Fin 1)))) hx
      have hxEq : x = ({(0 : Fin 1)} : Multiset (Fin 1)) := by
        simpa using hx'
      subst hxEq
      exact ⟨(0 : Fin 1), rfl⟩
    ·
      have hmrep : m = Multiset.replicate m.card (0 : Fin 1) := by
        refine Multiset.induction_on m ?_ ?_
        · simp
        · intro a s ih
          have ha : a = (0 : Fin 1) := by
            simpa using (Subsingleton.elim a (0 : Fin 1))
          subst ha
          -- goal: 0 ::ₘ s = replicate (card (0 ::ₘ s)) 0
          rw [Multiset.card_cons]
          -- goal: 0 ::ₘ s = replicate (Multiset.card s + 1) 0
          rw [Multiset.replicate_succ (a := (0 : Fin 1)) (n := Multiset.card s)]
          -- goal: 0 ::ₘ s = 0 ::ₘ replicate (Multiset.card s) 0
          rw [ih]
          -- simplify the remaining card
          simp [Multiset.card_replicate]

      calc
        (List.replicate m.card ({(0 : Fin 1)} : Multiset (Fin 1))).sum
            = m.card • ({(0 : Fin 1)} : Multiset (Fin 1)) := by
              simpa using (List.sum_replicate ({(0 : Fin 1)} : Multiset (Fin 1)) m.card)
        _ = Multiset.replicate m.card (0 : Fin 1) := by
              simpa using (Multiset.nsmul_singleton (a := (0 : Fin 1)) (n := m.card))
        _ = m := by
              simpa using hmrep.symm


theorem ball_A1_mono_radius (R₁ R₂ : ℕ) (h : R₁ ≤ R₂) : Ball R₁ (A 1) ⊆ Ball R₂ (A 1) := by
  intro m hm
  have hmcard : m.card ≤ R₁ := (ball_A1_iff_card_le (R := R₁) m).1 hm
  have hmcard' : m.card ≤ R₂ := le_trans hmcard h
  exact (ball_A1_iff_card_le (R := R₂) m).2 hmcard'

theorem doublyMacro_b2_replicate_mem_ball_from_digits (k a b c : ℕ) :
  let t : ℕ := 2 ^ (2 ^ k)
  let M := DoublyMacroSet 2
  a ≤ t → b ≤ t → c ≤ t →
    (Multiset.replicate (a * (t ^ 2) + b * t + c) (0 : Fin 1) : FreeAbelianMonoid 1)
      ∈ Ball (3 * t) (M ∪ (A 1)) := by
  classical
  dsimp
  intro ha hb hc

  let t : ℕ := 2 ^ (2 ^ k)
  let M : Set (FreeAbelianMonoid 1) := DoublyMacroSet 2
  let i : Fin 1 := 0

  have ha' : a ≤ t := by simpa [t] using ha
  have hb' : b ≤ t := by simpa [t] using hb
  have hc' : c ≤ t := by simpa [t] using hc

  have hgoal :
      (Multiset.replicate (a * (t ^ 2) + b * t + c) i : FreeAbelianMonoid 1)
        ∈ Ball (3 * t) (M ∪ (A 1)) := by

    let l : List (FreeAbelianMonoid 1) :=
      (List.replicate a (Multiset.replicate (t ^ 2) i) ++
        List.replicate b (Multiset.replicate t i)) ++
        List.replicate c (Multiset.replicate 1 i)

    refine ⟨l, ?_, ?_, ?_⟩

    · -- length bound
      have habc : a + b + c ≤ 3 * t := by
        omega
      have hl : l.length = a + b + c := by
        simp [l, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      simpa [hl] using habc

    · -- each entry is in `M ∪ A 1`
      intro x hx

      have h_t : (Multiset.replicate t i : FreeAbelianMonoid 1) ∈ M := by
        refine ⟨i, k, Nat.zero_le k, ?_⟩
        simpa [M, DoublyMacroSet, t]

      have h_t2 : (Multiset.replicate (t ^ 2) i : FreeAbelianMonoid 1) ∈ M := by
        refine ⟨i, k + 1, Nat.zero_le (k + 1), ?_⟩
        have hpow : t ^ 2 = 2 ^ (2 ^ (k + 1)) := by
          have : (2 ^ (2 ^ k)) ^ 2 = 2 ^ (2 ^ (k + 1)) := by
            calc
              (2 ^ (2 ^ k)) ^ 2 = 2 ^ ((2 ^ k) * 2) := by
                simpa using (pow_mul (2 : ℕ) (2 ^ k) 2).symm
              _ = 2 ^ (2 ^ (k + 1)) := by
                simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          simpa [t] using this
        simpa [M, DoublyMacroSet, hpow]

      rcases (by simpa [l] using hx) with hx1 | hx2
      · rcases hx1 with ⟨_, rfl⟩
        exact Or.inl h_t2
      · rcases hx2 with hx2 | hx3
        · rcases hx2 with ⟨_, rfl⟩
          exact Or.inl h_t
        · rcases hx3 with ⟨_, rfl⟩
          exact Or.inr ⟨i, rfl⟩

    · -- sum computation
      -- reduce `l.sum` to a sum of three `Multiset.replicate`s
      simp [l, List.sum_append, List.sum_replicate, Multiset.nsmul_replicate,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_one, Nat.one_mul,
        Nat.add_assoc]
      -- convert the singleton block
      simp [Multiset.nsmul_singleton]
      -- expand the RHS replicate to match the LHS
      rw [Multiset.replicate_add (a * t ^ 2) (b * t + c) i]
      rw [Multiset.replicate_add (b * t) c i]

  simpa [t, M, i] using hgoal


theorem doublyMacro_inter_ball_ncard (b x : ℕ) (hb : 2 ≤ b) (hx : b ≤ x) : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 := by
  classical
  have hb1 : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
  have hbpos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hxpos : 0 < x := lt_of_lt_of_le hbpos hx
  have hx0 : x ≠ 0 := Nat.ne_of_gt hxpos
  let k : ℕ := Nat.log b x
  have hkpos : 0 < k := Nat.log_pos hb1 hx
  have hk0 : k ≠ 0 := Nat.ne_of_gt hkpos
  let f : (Fin 1 × Fin (Nat.log b k + 1)) → FreeAbelianMonoid 1 := fun p =>
    Multiset.replicate (b ^ (b ^ p.2.1)) p.1
  have hS : DoublyMacroSet b ∩ Ball x (A 1) = Set.range f := by
    ext m
    constructor
    · intro hm
      rcases hm with ⟨hmM, hmB⟩
      rcases hmM with ⟨i, j, hj0, rfl⟩
      have hcard : (Multiset.replicate (b ^ (b ^ j)) i).card ≤ x :=
        (ball_A1_iff_card_le (R := x) (m := Multiset.replicate (b ^ (b ^ j)) i)).1 hmB
      have hpowle : b ^ (b ^ j) ≤ x := by
        simpa [Multiset.card_replicate] using hcard
      have hbpow_le_log : b ^ j ≤ Nat.log b x :=
        (Nat.pow_le_iff_le_log (b := b) hb1 (x := b ^ j) (y := x) hx0).1 hpowle
      have hbpow_le_k : b ^ j ≤ k := by
        simpa [k] using hbpow_le_log
      have hjle : j ≤ Nat.log b k :=
        (Nat.pow_le_iff_le_log (b := b) hb1 (x := j) (y := k) hk0).1 hbpow_le_k
      let j' : Fin (Nat.log b k + 1) := ⟨j, Nat.lt_succ_of_le hjle⟩
      refine ⟨⟨i, j'⟩, ?_⟩
      simp [f, j']
    · rintro ⟨p, rfl⟩
      constructor
      · refine ⟨p.1, p.2.1, Nat.zero_le _, rfl⟩
      · apply (ball_A1_iff_card_le (R := x) (m := Multiset.replicate (b ^ (b ^ p.2.1)) p.1)).2
        have hjle : p.2.1 ≤ Nat.log b k := by
          exact Nat.le_of_lt_succ p.2.2
        have hbpow_le_k : b ^ p.2.1 ≤ k :=
          Nat.pow_le_of_le_log (b := b) (x := p.2.1) (y := k) hk0 hjle
        have hpowpow_le_x : b ^ (b ^ p.2.1) ≤ x := by
          have : b ^ (b ^ p.2.1) ≤ x :=
            Nat.pow_le_of_le_log (b := b) (x := b ^ p.2.1) (y := x) hx0 (by simpa [k] using hbpow_le_k)
          exact this
        simpa [Multiset.card_replicate] using hpowpow_le_x
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hcard : b ^ (b ^ j.1) = b ^ (b ^ j'.1) := by
      simpa [f, Multiset.card_replicate] using congrArg Multiset.card h
    have hbpow_eq : b ^ j.1 = b ^ j'.1 := (Nat.pow_right_injective hb) hcard
    have hjval : j.1 = j'.1 := (Nat.pow_right_injective hb) hbpow_eq
    have hjFin : j = j' := Fin.ext hjval
    cases hjFin
    have hb0 : b ≠ 0 := by
      exact Nat.ne_of_gt hbpos
    have hpow0 : b ^ (b ^ j.1) ≠ 0 := pow_ne_zero _ hb0
    have hi : i = i' :=
      (Multiset.replicate_right_inj (a := i) (b := i') (n := b ^ (b ^ j.1)) hpow0).1 (by
        simpa [f] using h)
    exact Prod.ext hi rfl
  calc
    (DoublyMacroSet b ∩ Ball x (A 1)).ncard = (Set.range f).ncard := by
      simpa [hS]
    _ = Nat.card (Fin 1 × Fin (Nat.log b k + 1)) := Set.ncard_range_of_injective hf
    _ = Nat.log b k + 1 := by
      simp [Nat.card_prod, Nat.card_fin, k]

theorem fin1_multiset_eq_replicate_card (m : FreeAbelianMonoid 1) : m = Multiset.replicate m.card (0 : Fin 1) := by
  classical
  -- `Fin 1` is subsingleton, so every element is `0`.
  let f : Fin 1 → Fin 1 := fun _ => 0
  have hf : f = id := by
    funext x
    simpa [f] using (Subsingleton.elim (0 : Fin 1) x)
  -- Map by the constant function `f`.
  have hmap : Multiset.map f m = Multiset.replicate m.card (0 : Fin 1) := by
    simpa [f] using (Multiset.map_const' (s := m) (b := (0 : Fin 1)))
  -- But `f = id`, so the map is just `m`.
  simpa [hf] using hmap

theorem nat_le_pow3_exists_digits (t n : ℕ) (ht : 0 < t) (hn : n ≤ t ^ 3) :
  ∃ a b c : ℕ, a ≤ t ∧ b ≤ t ∧ c ≤ t ∧ n = a * (t ^ 2) + b * t + c := by
  classical
  let a : ℕ := n / (t ^ 2)
  let r1 : ℕ := n % (t ^ 2)
  let b : ℕ := r1 / t
  let c : ℕ := r1 % t
  refine ⟨a, b, c, ?_⟩
  -- bounds
  have hn' : n ≤ t ^ 2 * t := by
    simpa [pow_succ] using hn
  have ha' : n / (t ^ 2) ≤ t := Nat.div_le_of_le_mul' hn'
  have ha : a ≤ t := by
    simpa [a] using ha'
  have hr1lt : r1 < t ^ 2 := by
    simpa [r1] using (Nat.mod_lt n (pow_pos ht 2))
  have hr1le : r1 ≤ t * t := by
    have : r1 ≤ t ^ 2 := Nat.le_of_lt hr1lt
    simpa [pow_two, Nat.mul_assoc] using this
  have hb' : r1 / t ≤ t := Nat.div_le_of_le_mul' hr1le
  have hb : b ≤ t := by
    simpa [b] using hb'
  have hc : c ≤ t := by
    have hc_lt : c < t := by
      simpa [c] using (Nat.mod_lt r1 ht)
    exact Nat.le_of_lt hc_lt
  refine And.intro ha ?_
  refine And.intro hb ?_
  refine And.intro hc ?_
  -- equality
  have hn_decomp : n = a * (t ^ 2) + r1 := by
    -- from division algorithm
    -- Nat.div_add_mod gives: (t^2) * (n/(t^2)) + n%(t^2) = n
    -- rewrite
    simpa [a, r1, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.div_add_mod n (t ^ 2)).symm
  have hr1_decomp : r1 = b * t + c := by
    simpa [b, c, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Nat.div_add_mod r1 t).symm
  -- combine
  calc
    n = a * (t ^ 2) + r1 := hn_decomp
    _ = a * (t ^ 2) + (b * t + c) := by
      simpa [hr1_decomp]
    _ = a * (t ^ 2) + b * t + c := by
      omega


theorem doublyMacro_expansion_counterexample_b2 (k : ℕ) :
  let t : ℕ := 2 ^ (2 ^ k)
  let M := DoublyMacroSet 2
  Ball (t ^ 3) (A 1) ⊆ Ball (3 * t) (M ∪ (A 1)) := by
  classical
  dsimp
  set t : ℕ := 2 ^ (2 ^ k) with ht
  intro m hm
  have hn : m.card ≤ t ^ 3 := (ball_A1_iff_card_le (R := t ^ 3) m).1 hm
  have hmrep : m = Multiset.replicate m.card (0 : Fin 1) :=
    fin1_multiset_eq_replicate_card m
  have htpos : 0 < t := by
    have : 0 < 2 ^ (2 ^ k) := pow_pos (by decide : (0 : ℕ) < 2) (2 ^ k)
    simpa [ht] using this
  rcases nat_le_pow3_exists_digits t m.card htpos hn with ⟨a, b, c, ha, hb, hc, hcard⟩
  have hrep :
      (Multiset.replicate (a * (t ^ 2) + b * t + c) (0 : Fin 1) : FreeAbelianMonoid 1)
        ∈ Ball (3 * t) (DoublyMacroSet 2 ∪ (A 1)) := by
    -- use the macro-digit lemma, rewriting its internal `let`-bound `t` to our `t`
    simpa [ht.symm] using (doublyMacro_b2_replicate_mem_ball_from_digits k a b c) ha hb hc
  have hrep' :
      (Multiset.replicate m.card (0 : Fin 1) : FreeAbelianMonoid 1)
        ∈ Ball (3 * t) (DoublyMacroSet 2 ∪ (A 1)) := by
    simpa [hcard.symm] using hrep
  -- rewrite `m` as a replicate and conclude
  rw [hmrep]
  exact hrep'

theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h1 : n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
      have hpos : 1 ≤ 2 ^ n := by
        have h0 : 0 < 2 ^ n := by
          exact pow_pos (by decide : 0 < (2 : ℕ)) n
        exact (Nat.succ_le_iff).2 h0
      have h2 : 2 ^ n + 1 ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left hpos (2 ^ n)
      have h3 : n + 1 ≤ 2 ^ n + 2 ^ n := le_trans h1 h2
      simpa [Nat.succ_eq_add_one, pow_succ, Nat.mul_two, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h3

theorem nat_le_two_pow_two_pow (n : ℕ) : n ≤ 2 ^ (2 ^ n) := by
  have hn : n ≤ 2 ^ n := nat_le_two_pow n
  have hpow : 2 ^ n ≤ 2 ^ (2 ^ n) := by
    exact pow_le_pow_right' (a := 2) (by decide : (1 : ℕ) ≤ 2) hn
  exact le_trans hn hpow

theorem b2_exists_t_gt_mul_C2 (C₂ : ℝ) (hC₂ : 0 < C₂) :
  ∃ k : ℕ, (9 * C₂) < (2 ^ (2 ^ k) : ℝ) := by
  classical
  refine ⟨Nat.ceil (9 * C₂) + 1, ?_⟩
  have hle : (9 * C₂) ≤ (Nat.ceil (9 * C₂) : ℝ) := by
    exact Nat.le_ceil (9 * C₂)
  have hlt' : (Nat.ceil (9 * C₂) : ℝ) < (Nat.ceil (9 * C₂) : ℝ) + 1 := by
    have hpos : (0 : ℝ) < 1 := by norm_num
    exact lt_add_of_pos_right _ hpos
  have hlt : (9 * C₂) < (Nat.ceil (9 * C₂) : ℝ) + 1 := lt_of_le_of_lt hle hlt'
  have hk : ((Nat.ceil (9 * C₂) + 1 : ℕ) : ℝ) ≤ (2 ^ (2 ^ (Nat.ceil (9 * C₂) + 1)) : ℝ) := by
    have hk_nat : (Nat.ceil (9 * C₂) + 1 : ℕ) ≤ 2 ^ (2 ^ (Nat.ceil (9 * C₂) + 1)) :=
      nat_le_two_pow_two_pow (Nat.ceil (9 * C₂) + 1)
    exact_mod_cast hk_nat
  have hlt_k : (9 * C₂) < ((Nat.ceil (9 * C₂) + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hlt
  exact lt_of_lt_of_le hlt_k hk

theorem doublyMacro_b2_noninclusion_fails (C₂ : ℝ) (hC₂ : 0 < C₂) :
  ∃ s : ℕ, s ≥ 1 ∧
    let M := DoublyMacroSet 2
    let rs := Real.rpow s ((2 : ℝ) / (2 - 1))
    Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆ Ball s (M ∪ (A 1)) := by
  classical
  obtain ⟨k, hk⟩ := b2_exists_t_gt_mul_C2 C₂ hC₂
  let t : ℕ := 2 ^ (2 ^ k)
  have ht : (9 * C₂) < (t : ℝ) := by
    simpa [t] using hk
  let s : ℕ := 3 * t
  refine ⟨s, ?_, ?_⟩
  ·
    have htpos : 0 < t := by
      have h2pos : 0 < (2 : ℕ) := by decide
      simpa [t] using (pow_pos h2pos (2 ^ k))
    have hspos : 0 < s := by
      have h3pos : 0 < (3 : ℕ) := by decide
      simpa [s] using Nat.mul_pos h3pos htpos
    exact (Nat.succ_le_iff).2 hspos
  ·
    dsimp
    have hcounter : Ball (t ^ 3) (A 1) ⊆ Ball (3 * t) (DoublyMacroSet 2 ∪ (A 1)) := by
      simpa [t] using (doublyMacro_expansion_counterexample_b2 k)
    have htpos : 0 < t := by
      have h2pos : 0 < (2 : ℕ) := by decide
      simpa [t] using (pow_pos h2pos (2 ^ k))
    have ht3_ne : t ^ 3 ≠ 0 := by
      have : 0 < t ^ 3 := by
        exact pow_pos htpos 3
      exact Nat.ne_of_gt this
    have hxlt : C₂ * Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1)) < ((t ^ 3 : ℕ) : ℝ) := by
      rw [b2_rs_eq_sq s]
      have htRpos : 0 < (t : ℝ) := by exact_mod_cast htpos
      have ht2pos : 0 < (t : ℝ) ^ 2 := by
        simpa using (pow_pos htRpos 2)
      have hmul : (9 * C₂) * ((t : ℝ) ^ 2) < (t : ℝ) * ((t : ℝ) ^ 2) :=
        mul_lt_mul_of_pos_right ht ht2pos
      have hmul' : (9 * C₂) * ((t : ℝ) ^ 2) < (t : ℝ) ^ 3 := by
        simpa [pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hsimp : C₂ * (s : ℝ) ^ 2 = (9 * C₂) * ((t : ℝ) ^ 2) := by
        -- expand s and normalize the ring expression
        -- (s:ℝ) = (3:ℝ) * (t:ℝ)
        have hs' : (s : ℝ) = (3 : ℝ) * (t : ℝ) := by
          -- `Nat.cast_mul` gives ((3*t):ℝ) = 3 * t
          simpa [s] using (Nat.cast_mul 3 t : ((3 * t : ℕ) : ℝ) = (3 : ℝ) * (t : ℝ))
        -- rewrite using hs'
        -- and then use ring normalization
        --
        -- `pow_two` turns squares into multiplication
        --
        calc
          C₂ * (s : ℝ) ^ 2
              = C₂ * ((3 : ℝ) * (t : ℝ)) ^ 2 := by simpa [hs']
          _ = (9 * C₂) * ((t : ℝ) ^ 2) := by
              ring_nf
      simpa [hsimp, Nat.cast_pow] using hmul'
    have hfloor : Int.floor (C₂ * Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1))) < (t ^ 3 : ℤ) := by
      exact (Int.floor_lt).2 (by simpa using hxlt)
    have htoNat_lt : Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1)))) < t ^ 3 := by
      have hiff :=
        (Int.toNat_lt'' (m := Int.floor (C₂ * Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1)))) (n := t ^ 3)
          ht3_ne)
      exact hiff.2 hfloor
    have hrad_le : 1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1)))) ≤ t ^ 3 := by
      have h' : Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1)))) + 1 ≤ t ^ 3 :=
        Nat.succ_le_of_lt htoNat_lt
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h'
    have hmono :
        Ball (1 + Int.toNat (Int.floor (C₂ * Real.rpow (s : ℝ) ((2 : ℝ) / (2 - 1))))) (A 1)
          ⊆ Ball (t ^ 3) (A 1) :=
      ball_A1_mono_radius _ _ hrad_le
    have hcounter' : Ball (t ^ 3) (A 1) ⊆ Ball s (DoublyMacroSet 2 ∪ (A 1)) := by
      simpa [s] using hcounter
    exact hmono.trans hcounter'

theorem doublyMacro_expansion_bounds_false_b2: ¬ (∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), s ≥ 1 →
      let M := DoublyMacroSet 2
      let rs := Real.rpow s ((2 : ℝ) / (2 - 1))
      (Ball (Int.toNat (Int.ceil (C₁ * rs))) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
        ¬ (Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆ Ball s (M ∪ (A 1))))
  ) := by
  intro h
  rcases h with ⟨C₁, C₂, hC₁, hC₂, h⟩
  rcases doublyMacro_b2_noninclusion_fails C₂ hC₂ with ⟨s, hs, hsIncl⟩
  have hsProp := h s hs
  have hsProp' :
      (Ball (Int.toNat (Int.ceil (C₁ * Real.rpow s ((2 : ℝ) / (2 - 1))))) (A 1) ⊆
          Ball s (DoublyMacroSet 2 ∪ (A 1))) ∧
        ¬
          (Ball (1 + Int.toNat (Int.floor (C₂ * Real.rpow s ((2 : ℝ) / (2 - 1))))) (A 1) ⊆
            Ball s (DoublyMacroSet 2 ∪ (A 1))) := by
    simpa using hsProp
  have hsIncl' :
      Ball (1 + Int.toNat (Int.floor (C₂ * Real.rpow s ((2 : ℝ) / (2 - 1))))) (A 1) ⊆
        Ball s (DoublyMacroSet 2 ∪ (A 1)) := by
    simpa using hsIncl
  exact hsProp'.2 hsIncl'

theorem nat_log_real_bounds (b x : ℕ) (hb : 2 ≤ b) (hx : b ≤ x) :
    (Real.log (x : ℝ)) / (2 * Real.log (b : ℝ)) ≤ (Nat.log b x : ℝ) ∧
    (Nat.log b x : ℝ) ≤ (Real.log (x : ℝ)) / (Real.log (b : ℝ)) := by
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have hx2 : 2 ≤ x := le_trans hb hx
  have hxpos : 0 < x := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hx2
  have hx0 : x ≠ 0 := Nat.ne_of_gt hxpos
  have hbposNat : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast hbposNat
  have hlogbpos : 0 < Real.log (b : ℝ) := by
    have hb1R : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast hb1
    simpa using Real.log_pos hb1R

  constructor
  · -- lower bound
    have hxRpos : (0 : ℝ) < (x : ℝ) := by
      exact_mod_cast hxpos

    have hltNat : x < b ^ (Nat.log b x).succ := Nat.lt_pow_succ_log_self hb1 x
    have hltR : (x : ℝ) < (b : ℝ) ^ (Nat.log b x).succ := by
      have : ((x : ℕ) : ℝ) < ((b ^ (Nat.log b x).succ : ℕ) : ℝ) := by
        exact_mod_cast hltNat
      simpa [Nat.cast_pow] using this

    have hloglt : Real.log (x : ℝ) < Real.log ((b : ℝ) ^ (Nat.log b x).succ) := by
      exact Real.log_lt_log hxRpos hltR

    have hloglt' : Real.log (x : ℝ) < (Nat.log b x).succ * Real.log (b : ℝ) := by
      simpa [Real.log_pow] using hloglt

    have hkpos : 0 < Nat.log b x := Nat.log_pos hb1 hx
    have hk1 : (1 : ℝ) ≤ (Nat.log b x : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hkpos)

    have hk2' : ((Nat.log b x).succ : ℝ) ≤ 2 * (Nat.log b x : ℝ) := by
      -- succ cast is k+1
      have hk2 : (Nat.log b x : ℝ) + 1 ≤ 2 * (Nat.log b x : ℝ) := by
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using (add_one_le_two_mul hk1)
      simpa [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using hk2

    have hlogle2 : Real.log (x : ℝ) ≤ (2 * (Nat.log b x : ℝ)) * Real.log (b : ℝ) := by
      have h0 : (Real.log (x : ℝ)) ≤ ((Nat.log b x).succ : ℝ) * Real.log (b : ℝ) := by
        exact le_of_lt hloglt'
      have h1 : ((Nat.log b x).succ : ℝ) * Real.log (b : ℝ) ≤ (2 * (Nat.log b x : ℝ)) * Real.log (b : ℝ) := by
        have hlogbnonneg : 0 ≤ Real.log (b : ℝ) := le_of_lt hlogbpos
        exact mul_le_mul_of_nonneg_right hk2' hlogbnonneg
      exact le_trans h0 h1

    have hdenpos : 0 < (2 * Real.log (b : ℝ)) := by
      nlinarith [hlogbpos]

    -- divide by positive 2*log b
    have : Real.log (x : ℝ) / (2 * Real.log (b : ℝ)) ≤ (Nat.log b x : ℝ) := by
      refine (div_le_iff₀ hdenpos).2 ?_
      -- goal: log x ≤ (Nat.log b x) * (2*log b)
      -- rewrite RHS to match hlogle2
      simpa [mul_assoc, mul_left_comm, mul_comm, two_mul] using hlogle2
    exact this

  · -- upper bound
    have hpowNat : b ^ Nat.log b x ≤ x := Nat.pow_log_le_self b hx0
    have hpowR : (b : ℝ) ^ Nat.log b x ≤ (x : ℝ) := by
      have : ((b ^ Nat.log b x : ℕ) : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast hpowNat
      simpa [Nat.cast_pow] using this

    have hlogle : (Nat.log b x : ℝ) * Real.log (b : ℝ) ≤ Real.log (x : ℝ) := by
      simpa using (Real.le_log_of_pow_le hbpos hpowR)

    have : (Nat.log b x : ℝ) ≤ Real.log (x : ℝ) / Real.log (b : ℝ) := by
      refine (le_div_iff₀ hlogbpos).2 ?_
      simpa [mul_assoc, mul_left_comm, mul_comm] using hlogle
    exact this

theorem doublyMacro_loglog_density (b : ℕ) (hb : 2 ≤ b) : ∃ (d1 d2 : ℝ), ∀ (x : ℕ), x ≥ b ^ b → 0 < d1 ∧ 0 < d2 ∧ d1 * (Real.log (Real.log x)) ≤ (DoublyMacroSet b ∩ Ball x (A 1)).ncard ∧ (DoublyMacroSet b ∩ Ball x (A 1)).ncard ≤ d2 * (Real.log (Real.log x)) := by
  classical
  -- basic facts about `b`
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
  have hb1R : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hbposR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hb1R
  have hlogb_ne : Real.log (b : ℝ) ≠ 0 := ne_of_gt hlogb

  -- c0 := log(log(b^b)) is positive
  have h4_le_bpow : (4 : ℕ) ≤ b ^ b := by
    have hpow1 : (2 : ℕ) ^ 2 ≤ (2 : ℕ) ^ b := by
      exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) hb
    have hpow2 : (2 : ℕ) ^ b ≤ b ^ b := by
      exact pow_le_pow_left' hb b
    have hpow : (2 : ℕ) ^ 2 ≤ b ^ b := le_trans hpow1 hpow2
    simpa using hpow
  have hbpow_pos : 0 < b ^ b := lt_of_lt_of_le (by decide : (0 : ℕ) < 4) h4_le_bpow
  have hbpow_posR : (0 : ℝ) < (b ^ b : ℝ) := by exact_mod_cast hbpow_pos
  have hexp1_lt4 : Real.exp (1 : ℝ) < (4 : ℝ) := by
    have h : Real.exp (1 : ℝ) < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have h2 : (2.7182818286 : ℝ) < (4 : ℝ) := by norm_num
    exact lt_trans h h2
  have hexp1_ltbpow : Real.exp (1 : ℝ) < (b ^ b : ℝ) := by
    have h4le : (4 : ℝ) ≤ (b ^ b : ℝ) := by exact_mod_cast h4_le_bpow
    exact lt_of_lt_of_le hexp1_lt4 h4le
  have hone_lt_log_bpow : (1 : ℝ) < Real.log (b ^ b : ℝ) := by
    have := (Real.lt_log_iff_exp_lt hbpow_posR).2 hexp1_ltbpow
    simpa using this
  have hc0 : 0 < Real.log (Real.log (b ^ b : ℝ)) := Real.log_pos hone_lt_log_bpow

  -- constants
  let d1 : ℝ := (1 : ℝ) / (2 * Real.log (b : ℝ))
  let c0 : ℝ := Real.log (Real.log (b ^ b : ℝ))
  let Cb : ℝ := (1 : ℝ) - Real.log (Real.log (b : ℝ)) / Real.log (b : ℝ)
  let d2 : ℝ := (1 : ℝ) / Real.log (b : ℝ) + |Cb| / c0

  refine ⟨d1, d2, ?_⟩
  intro x hx

  -- show b ≤ x
  have hb1le : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hb0 : b ≠ 0 := Nat.ne_of_gt hbpos
  have hb_le_bpow : b ≤ b ^ b := le_self_pow hb1le hb0
  have hx_ge_b : b ≤ x := le_trans hb_le_bpow hx

  -- positivity facts for x
  have hxpos : 0 < x := lt_of_lt_of_le hbpos hx_ge_b
  have hxposR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hxpos
  have hx0 : x ≠ 0 := Nat.ne_of_gt hxpos

  -- rewrite ncard
  have hncard : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = Nat.log b (Nat.log b x) + 1 :=
    doublyMacro_inter_ball_ncard b x hb hx_ge_b
  let k : ℕ := Nat.log b x
  let l : ℕ := Nat.log b k
  have hncard' : (DoublyMacroSet b ∩ Ball x (A 1)).ncard = l + 1 := by
    simpa [k, l, Nat.add_assoc] using hncard

  -- some logs are positive
  have hk_pos : 0 < k := Nat.log_pos hb1 hx_ge_b
  have hk_posR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_ne0 : k ≠ 0 := Nat.ne_of_gt hk_pos

  have hlogx_pos : 0 < Real.log (x : ℝ) := by
    have hx1R : (1 : ℝ) < (x : ℝ) := by
      have : (1 : ℕ) < x := lt_of_lt_of_le hb1 hx_ge_b
      exact_mod_cast this
    exact Real.log_pos hx1R

  -- c0 ≤ log(log x)
  have hc0_le : c0 ≤ Real.log (Real.log (x : ℝ)) := by
    have hlog_bpow_le : Real.log (b ^ b : ℝ) ≤ Real.log (x : ℝ) := by
      have hbpow_le : (b ^ b : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      exact Real.log_le_log hbpow_posR hbpow_le
    have hloglog_le : Real.log (Real.log (b ^ b : ℝ)) ≤ Real.log (Real.log (x : ℝ)) := by
      have hlogbpow_pos : (0 : ℝ) < Real.log (b ^ b : ℝ) :=
        lt_trans (by norm_num : (0 : ℝ) < 1) hone_lt_log_bpow
      exact Real.log_le_log hlogbpow_pos hlog_bpow_le
    simpa [c0] using hloglog_le

  -- positivity of d1 and d2
  have hd1pos : 0 < d1 := by
    dsimp [d1]
    have hden : 0 < (2 : ℝ) * Real.log (b : ℝ) := by
      have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact mul_pos h2 hlogb
    exact one_div_pos.mpr hden

  have hd2pos : 0 < d2 := by
    dsimp [d2]
    have h1 : 0 < (1 : ℝ) / Real.log (b : ℝ) := one_div_pos.mpr hlogb
    have hc0pos : 0 < c0 := by simpa [c0] using hc0
    have h2nonneg : 0 ≤ |Cb| / c0 := div_nonneg (abs_nonneg Cb) (le_of_lt hc0pos)
    linarith

  -- LOWER BOUND
  have h_lower : d1 * Real.log (Real.log (x : ℝ)) ≤ (l + 1 : ℝ) := by
    have hk_lt : k < b ^ (l + 1) := by
      simpa [l, Nat.succ_eq_add_one] using (Nat.lt_pow_succ_log_self hb1 k)
    have hk_succ_le : k.succ ≤ b ^ (l + 1) := Nat.succ_le_of_lt hk_lt
    have hx_lt : x < b ^ k.succ := by
      simpa [k] using (Nat.lt_pow_succ_log_self hb1 x)
    have hx_lt2 : x < b ^ (b ^ (l + 1)) := by
      have hpow_mono : b ^ k.succ ≤ b ^ (b ^ (l + 1)) := pow_le_pow_right' hb1le hk_succ_le
      exact lt_of_lt_of_le hx_lt hpow_mono
    have hx_lt2R : (x : ℝ) < (b : ℝ) ^ (b ^ (l + 1)) := by
      have : (x : ℝ) < (b ^ (b ^ (l + 1)) : ℕ) := by exact_mod_cast hx_lt2
      simpa [Nat.cast_pow] using this
    have hlog_lt : Real.log (x : ℝ) < Real.log ((b : ℝ) ^ (b ^ (l + 1))) :=
      Real.log_lt_log hxposR hx_lt2R
    have hlog_le : Real.log (x : ℝ) ≤ ((b ^ (l + 1) : ℕ) : ℝ) * Real.log (b : ℝ) := by
      have : Real.log ((b : ℝ) ^ (b ^ (l + 1))) = ((b ^ (l + 1) : ℕ) : ℝ) * Real.log (b : ℝ) := by
        simp [Real.log_pow]
      exact le_of_lt (by simpa [this] using hlog_lt)
    have hloglog_le :
        Real.log (Real.log (x : ℝ)) ≤ Real.log (((b ^ (l + 1) : ℕ) : ℝ) * Real.log (b : ℝ)) :=
      Real.log_le_log hlogx_pos hlog_le
    -- replace log b by b using log b ≤ b
    have hlogb_le_b : Real.log (b : ℝ) ≤ (b : ℝ) :=
      Real.log_le_self (by positivity : (0 : ℝ) ≤ (b : ℝ))
    have hbpow_nonneg : (0 : ℝ) ≤ ((b ^ (l + 1) : ℕ) : ℝ) := by positivity
    have hmul_le : ((b ^ (l + 1) : ℕ) : ℝ) * Real.log (b : ℝ) ≤ ((b ^ (l + 1) : ℕ) : ℝ) * (b : ℝ) :=
      mul_le_mul_of_nonneg_left hlogb_le_b hbpow_nonneg
    have hpos_mul : 0 < ((b ^ (l + 1) : ℕ) : ℝ) * Real.log (b : ℝ) := by
      have hbpow_posNat : 0 < b ^ (l + 1) := pow_pos hbpos _
      have hbpow_posR : (0 : ℝ) < ((b ^ (l + 1) : ℕ) : ℝ) := by exact_mod_cast hbpow_posNat
      exact mul_pos hbpow_posR hlogb
    have hloglog_le2 :
        Real.log (Real.log (x : ℝ)) ≤ Real.log (((b ^ (l + 1) : ℕ) : ℝ) * (b : ℝ)) :=
      le_trans hloglog_le (Real.log_le_log hpos_mul hmul_le)
    -- simplify RHS to (l+2)*log b
    have hloglog_le3 : Real.log (Real.log (x : ℝ)) ≤ (l + 2 : ℝ) * Real.log (b : ℝ) := by
      have htmp :
          Real.log (Real.log (x : ℝ)) ≤ Real.log ((b : ℝ) ^ (l + 1) * (b : ℝ)) := by
        simpa [Nat.cast_pow] using hloglog_le2
      have hprod : (b : ℝ) ^ (l + 2) = (b : ℝ) ^ (l + 1) * (b : ℝ) := by
        simpa [Nat.add_assoc] using (pow_succ (b : ℝ) (l + 1))
      have hRHS : Real.log ((b : ℝ) ^ (l + 1) * (b : ℝ)) = (l + 2 : ℝ) * Real.log (b : ℝ) := by
        calc
          Real.log ((b : ℝ) ^ (l + 1) * (b : ℝ)) = Real.log ((b : ℝ) ^ (l + 2)) := by
            simpa [hprod]
          _ = (l + 2 : ℝ) * Real.log (b : ℝ) := by
            simp [Real.log_pow]
      simpa [hRHS] using htmp

    have hlin : (l + 2 : ℝ) ≤ (2 : ℝ) * (l + 1 : ℝ) := by
      nlinarith
    have hloglog_le4 :
        Real.log (Real.log (x : ℝ)) ≤ (2 : ℝ) * (l + 1 : ℝ) * Real.log (b : ℝ) := by
      have := mul_le_mul_of_nonneg_right hlin (le_of_lt hlogb)
      have := le_trans hloglog_le3 this
      simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
    have hden : 0 < (2 : ℝ) * Real.log (b : ℝ) := by
      have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact mul_pos h2 hlogb
    have hdiv : Real.log (Real.log (x : ℝ)) / (2 * Real.log (b : ℝ)) ≤ (l + 1 : ℝ) :=
      (div_le_iff₀ hden).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hloglog_le4)
    dsimp [d1]
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

  -- UPPER BOUND
  have h_upper : (l + 1 : ℝ) ≤ d2 * Real.log (Real.log (x : ℝ)) := by
    have hb_le_k : b ≤ k := by
      have : b ^ b ≤ x := hx
      simpa [k] using (Nat.le_log_of_pow_le hb1 this)

    have hl_le : (l : ℝ) ≤ Real.log (k : ℝ) / Real.log (b : ℝ) := by
      have hk_bounds := nat_log_real_bounds b k hb hb_le_k
      simpa [l] using hk_bounds.2

    have hk_le : (k : ℝ) ≤ Real.log (x : ℝ) / Real.log (b : ℝ) := by
      have hx_bounds := nat_log_real_bounds b x hb hx_ge_b
      simpa [k] using hx_bounds.2

    have hlogk_le : Real.log (k : ℝ) ≤ Real.log (Real.log (x : ℝ) / Real.log (b : ℝ)) :=
      Real.log_le_log hk_posR hk_le

    have hlogx_ne : Real.log (x : ℝ) ≠ 0 := ne_of_gt hlogx_pos
    have hlog_div :
        Real.log (Real.log (x : ℝ) / Real.log (b : ℝ)) =
          Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ)) := by
      simpa using (Real.log_div hlogx_ne hlogb_ne)

    have hlogk_le' :
        Real.log (k : ℝ) ≤ Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ)) := by
      simpa [hlog_div] using hlogk_le

    have hdiv_le :
        Real.log (k : ℝ) / Real.log (b : ℝ) ≤
          (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ))) / Real.log (b : ℝ) := by
      exact div_le_div_of_nonneg_right hlogk_le' (le_of_lt hlogb)

    have hl_le2 :
        (l : ℝ) ≤
          (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ))) / Real.log (b : ℝ) :=
      le_trans hl_le hdiv_le

    have hl1_le :
        (l : ℝ) + 1 ≤
          (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ))) / Real.log (b : ℝ) + 1 := by
      linarith [hl_le2]

    have hl1_le' :
        (l + 1 : ℝ) ≤
          (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + Cb := by
      have :
          (Real.log (Real.log (x : ℝ)) - Real.log (Real.log (b : ℝ))) / Real.log (b : ℝ) + 1 =
            (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + Cb := by
        dsimp [Cb]
        ring
      simpa [this, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hl1_le

    have hl1_abs :
        (l + 1 : ℝ) ≤ (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + |Cb| := by
      have hCb : Cb ≤ |Cb| := le_abs_self Cb
      have h2 :
          (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + Cb ≤
            (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + |Cb| := by
        nlinarith [hCb]
      exact le_trans hl1_le' h2

    have hc0pos : 0 < c0 := by simpa [c0] using hc0
    have habs_le : |Cb| ≤ (|Cb| / c0) * Real.log (Real.log (x : ℝ)) := by
      have hc0ne : (c0 : ℝ) ≠ 0 := ne_of_gt hc0pos
      have hmul : (|Cb| / c0) * c0 = |Cb| := by
        field_simp [hc0ne]
      have hmul_nonneg : 0 ≤ |Cb| / c0 := div_nonneg (abs_nonneg Cb) (le_of_lt hc0pos)
      have h' : (|Cb| / c0) * c0 ≤ (|Cb| / c0) * Real.log (Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hc0_le hmul_nonneg
      -- rewrite left side
      simpa [hmul] using h'

    have hl1_abs' :
        (l + 1 : ℝ) ≤
          (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + (|Cb| / c0) * Real.log (Real.log (x : ℝ)) := by
      have h' :
          (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + |Cb| ≤
            (1 / Real.log (b : ℝ)) * Real.log (Real.log (x : ℝ)) + (|Cb| / c0) * Real.log (Real.log (x : ℝ)) := by
        nlinarith [habs_le]
      exact le_trans hl1_abs h'

    -- finalize
    dsimp [d2]
    have hmul_add :
        ((Real.log (b : ℝ))⁻¹ + |Cb| * (c0 : ℝ)⁻¹) * Real.log (Real.log (x : ℝ)) =
          (Real.log (b : ℝ))⁻¹ * Real.log (Real.log (x : ℝ)) + |Cb| * (c0 : ℝ)⁻¹ * Real.log (Real.log (x : ℝ)) := by
      ring
    -- simplify hl1_abs' to match the RHS of hmul_add, then rewrite
    have hl1_abs'' :
        (l + 1 : ℝ) ≤
          (Real.log (b : ℝ))⁻¹ * Real.log (Real.log (x : ℝ)) + |Cb| * (c0 : ℝ)⁻¹ * Real.log (Real.log (x : ℝ)) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hl1_abs'
    -- now rewrite goal RHS
    have :
        (l + 1 : ℝ) ≤ ((Real.log (b : ℝ))⁻¹ + |Cb| * (c0 : ℝ)⁻¹) * Real.log (Real.log (x : ℝ)) := by
      -- rewrite with hmul_add
      simpa [hmul_add] using hl1_abs''
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  refine ⟨hd1pos, hd2pos, ?_, ?_⟩
  ·
    have : d1 * Real.log (Real.log (x : ℝ)) ≤ (l + 1 : ℝ) := h_lower
    simpa [hncard', Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using this
  ·
    have : (l + 1 : ℝ) ≤ d2 * Real.log (Real.log (x : ℝ)) := h_upper
    simpa [hncard', Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using this

theorem theorem5_false_b2: ¬ (let M := DoublyMacroSet 2
  (∃ (d1 d2 : ℝ), ∀ (x : ℕ), (x ≥ 2 ^ 2) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ (Ball x (A 1))).ncard
      ∧ (M ∩ (Ball x (A 1))).ncard ≤ d2 * (Real.log (Real.log x))) ∧
  (∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    (∀ (s : ℕ), (s ≥ 1) →
      let rs := Real.rpow s ((2 : ℝ) / (2 - 1))
      (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
        ¬ (Ball (1 + Int.toNat <| Int.floor <| C₂ * rs)) (A 1) ⊆ Ball s (M ∪ (A 1)))
    )
  ) := by
  intro h
  have h' :
      (∃ d1 d2 : ℝ,
          ∀ x : ℕ,
            x ≥ 2 ^ 2 →
              0 < d1 ∧
                0 < d2 ∧
                  d1 * Real.log (Real.log x) ≤
                      (DoublyMacroSet 2 ∩ Ball x (A 1)).ncard ∧
                    (DoublyMacroSet 2 ∩ Ball x (A 1)).ncard ≤ d2 * Real.log (Real.log x)) ∧
        (∃ C₁ C₂ : ℝ,
            0 < C₁ ∧
              0 < C₂ ∧
                ∀ s : ℕ,
                  s ≥ 1 →
                    let rs := Real.rpow s ((2 : ℝ) / (2 - 1))
                    (Ball (Int.toNat <| Int.ceil <| C₁ * rs) (A 1) ⊆
                          Ball s (DoublyMacroSet 2 ∪ A 1)) ∧
                      ¬Ball (1 + Int.toNat <| Int.floor <| C₂ * rs) (A 1) ⊆
                          Ball s (DoublyMacroSet 2 ∪ A 1)) := by
    simpa using h
  rcases h' with ⟨_, hC⟩
  rcases hC with ⟨C₁, C₂, hC₁, hC₂, hforall⟩
  apply doublyMacro_expansion_bounds_false_b2
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro s hs
  simpa using (hforall s hs)


theorem theorem5_not_forall: ¬ (∀ (b : ℕ) (hb : 2 ≤ b),
    let M := DoublyMacroSet b
    (∃ (d1 d2 : ℝ), ∀ (x : ℕ), x ≥ b ^ b → 0 < d1 ∧ 0 < d2
        ∧ d1 * (Real.log (Real.log x)) ≤ (M ∩ Ball x (A 1)).ncard
        ∧ (M ∩ Ball x (A 1)).ncard ≤ d2 * (Real.log (Real.log x))) ∧
    ∃ C₁ C₂ : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧
      ∀ (s : ℕ), s ≥ 1 →
        let rs := Real.rpow s ((b : ℝ) / (b - 1))
        (Ball (Int.toNat (Int.ceil (C₁ * rs))) (A 1) ⊆ Ball s (M ∪ (A 1))) ∧
          ¬ (Ball (1 + Int.toNat (Int.floor (C₂ * rs))) (A 1) ⊆ Ball s (M ∪ (A 1)))
    ) := by
  intro h
  have h2 := h 2 (by exact le_rfl)
  exact theorem5_false_b2 (by simpa using h2)

