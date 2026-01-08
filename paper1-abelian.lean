import Mathlib

open scoped BigOperators

abbrev FreeAbelianMonoid (n : ℕ) := Multiset (Fin n)

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) : Set (FreeAbelianMonoid n) :=
  {m | ∃ l : List (FreeAbelianMonoid n), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

def A (n : ℕ) : Set (FreeAbelianMonoid n) :=
  { {i} | i : Fin n}

theorem theorem_1_exponential_expansion
  (n b : ℕ)
  (hb : 2 ≤ b) :
  ∃ (G : Set (FreeAbelianMonoid n)) (D : ℕ),
    (∀ s : ℕ, (s ≥ 3 * n * (b - 1)) →
      let r := Int.toNat <| Int.floor <| Real.rpow (b : ℝ) ((s : ℝ) / (n * (b - 1)) - 1)
      (Ball r (A n) ⊆ (Ball s G))) ∧
    (∀ r : ℕ, 2 ≤ r →
      (G ∩ (Ball r (A n))).ncard ≤ D * n * (Real.log r)) :=
    sorry

theorem theorem_2_quasi_exponential_expansion
  (n : ℕ)
  (G : Set (FreeAbelianMonoid n))
  (c q : ℝ) :
  (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) →
    (∃ (K : ℕ), ∀ (s : ℕ),
      let r := Int.toNat <| Int.floor <| Real.exp (K * s * (Real.log s))
      Ball r (A n) ⊆ Ball s G) :=
    sorry

noncomputable def Dlog2 : ℕ := ⌈(2 : ℝ) / Real.log 2⌉₊


theorem Ball_add_mem (n R S : ℕ) (X : Set (FreeAbelianMonoid n)) (m m' : FreeAbelianMonoid n) :
  m ∈ Ball R X → m' ∈ Ball S X → m + m' ∈ Ball (R + S) X := by
  intro hm hm'
  rcases hm with ⟨l, hlR, hXl, hsuml⟩
  rcases hm' with ⟨l', hlS, hXl', hsuml'⟩
  refine ⟨l ++ l', ?_, ?_, ?_⟩
  · -- length bound
    simpa [Ball, List.length_append] using Nat.add_le_add hlR hlS
  · -- membership
    intro x hx
    have hx' : x ∈ l ∨ x ∈ l' := by
      simpa [List.mem_append] using hx
    cases hx' with
    | inl h =>
        exact hXl x h
    | inr h =>
        exact hXl' x h
  · -- sum
    simpa [List.sum_append, hsuml, hsuml']

theorem Ball_mono_radius (n R S : ℕ) (X : Set (FreeAbelianMonoid n)) (hRS : R ≤ S) :
  Ball R X ⊆ Ball S X := by
  intro m hm
  rcases hm with ⟨l, hlR, hlX, hlSum⟩
  refine ⟨l, ?_, hlX, hlSum⟩
  exact le_trans hlR hRS


theorem Ball_sum_finset_mem (n : ℕ) (X : Set (FreeAbelianMonoid n)) (k : ℕ)
  (s : Finset (Fin n)) (f : Fin n → FreeAbelianMonoid n) :
  (∀ i ∈ s, f i ∈ Ball k X) →
    (∑ i ∈ s, f i) ∈ Ball (s.card * k) X := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro hs
    simp [Ball]
  · intro a s ha ih hs
    have ha_mem : f a ∈ Ball k X := hs a (by simp)
    have hs_mem : ∀ i ∈ s, f i ∈ Ball k X := by
      intro i hi
      exact hs i (by simp [hi])
    have hsum_mem : (∑ i ∈ s, f i) ∈ Ball (s.card * k) X := ih hs_mem
    have hadd : f a + (∑ i ∈ s, f i) ∈ Ball (k + s.card * k) X :=
      Ball_add_mem n k (s.card * k) X (f a) (∑ i ∈ s, f i) ha_mem hsum_mem
    have hRad : k + s.card * k = (insert a s).card * k := by
      calc
        k + s.card * k = s.card * k + k := by simpa [Nat.add_comm]
        _ = (s.card + 1) * k := by
          simpa [Nat.succ_eq_add_one] using (Nat.succ_mul s.card k).symm
        _ = (insert a s).card * k := by
          -- use the standard card formula for insert
          simpa [Finset.card_insert_of_not_mem ha]
    have hadd' : f a + (∑ i ∈ s, f i) ∈ Ball ((insert a s).card * k) X := by
      simpa [hRad] using hadd
    simpa [Finset.sum_insert, ha] using hadd'

def Gpow (n b : ℕ) : Set (FreeAbelianMonoid n) :=
  {m | ∃ i : Fin n, ∃ k : ℕ, m = Multiset.replicate (b ^ k) i}

theorem exists_pow_list_sum (b n : ℕ) (hb : 1 < b) :
  ∃ l : List ℕ,
    (∀ x ∈ l, ∃ k : ℕ, x = b ^ k) ∧
    l.length ≤ (b - 1) * (Nat.log b n + 1) ∧
    l.sum = n := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨[], ?_, ?_, ?_⟩
    · intro x hx
      cases hx
    · simp
    · simp
  ·
    have hn0 : n ≠ 0 := hn
    let ds : List ℕ := Nat.digits b n
    let g : Fin ds.length → List ℕ := fun i => List.replicate (ds.get i) (b ^ (i : ℕ))
    let L : List (List ℕ) := ds.mapIdx (fun i d => List.replicate d (b ^ i))
    have hL : L = List.ofFn g := by
      simpa [L, g] using (List.mapIdx_eq_ofFn ds (fun i d => List.replicate d (b ^ i)))
    have hlen_flat : L.flatten.length = (L.map List.length).sum := by
      simpa using (List.length_flatten L)
    have hsum_flat : L.flatten.sum = (L.map List.sum).sum := by
      simpa using (List.sum_flatten L)
    refine ⟨L.flatten, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_flatten.1 hx with ⟨l', hl', hx'⟩
      have hl_ofFn : l' ∈ List.ofFn g := by
        simpa [hL] using hl'
      have hl_range : l' ∈ Set.range g := (List.mem_ofFn' (f := g) (a := l')).1 hl_ofFn
      rcases hl_range with ⟨i, rfl⟩
      dsimp [g] at hx'
      have hxpow : x = b ^ (i : ℕ) := (List.mem_replicate.1 hx').2
      exact ⟨(i : ℕ), hxpow⟩
    · -- length bound
      have h_each : ∀ x ∈ L.map List.length, x ≤ b - 1 := by
        intro x hx
        rcases List.mem_map.1 hx with ⟨l', hl', rfl⟩
        have hl_ofFn : l' ∈ List.ofFn g := by
          simpa [hL] using hl'
        have hl_range : l' ∈ Set.range g := (List.mem_ofFn' (f := g) (a := l')).1 hl_ofFn
        rcases hl_range with ⟨i, rfl⟩
        -- reduce to bound on digit
        simp [g]
        have hlt' : (Nat.digits b n).get i < b := Nat.digits_lt_base hb (List.get_mem (Nat.digits b n) i)
        have hlt : ds.get i < b := by
          simpa [ds] using hlt'
        exact Order.le_sub_one_of_lt hlt
      have hsum_le : (L.map List.length).sum ≤ (L.map List.length).length * (b - 1) := by
        simpa using
          (List.sum_le_card_nsmul (l := L.map List.length) (n := b - 1) (h := h_each))
      have hLlen : L.length = ds.length := by
        simpa [L] using (List.length_mapIdx (l := ds) (f := fun i d => List.replicate d (b ^ i)))
      have hdslen : ds.length = Nat.log b n + 1 := by
        simpa [ds] using (Nat.digits_len (b := b) (n := n) hb hn0)
      calc
        L.flatten.length = (L.map List.length).sum := hlen_flat
        _ ≤ (L.map List.length).length * (b - 1) := hsum_le
        _ = L.length * (b - 1) := by simp
        _ = ds.length * (b - 1) := by simpa [hLlen]
        _ = (Nat.log b n + 1) * (b - 1) := by simpa [hdslen]
        _ = (b - 1) * (Nat.log b n + 1) := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · -- sum
      have hmap_sum : L.map List.sum = ds.mapIdx (fun i d => d * b ^ i) := by
        -- rewrite both sides as `ofFn` on `Fin ds.length`
        have hleft : L.map List.sum = List.ofFn (fun i : Fin ds.length => ds.get i * b ^ (i : ℕ)) := by
          calc
            L.map List.sum = (List.ofFn g).map List.sum := by simpa [hL]
            _ = List.ofFn (List.sum ∘ g) := by
              simpa using (List.map_ofFn (f := g) (g := List.sum))
            _ = List.ofFn (fun i : Fin ds.length => ds.get i * b ^ (i : ℕ)) := by
              refine congrArg List.ofFn ?_
              funext i
              simp [Function.comp, g, List.sum_const_nat]
        have hright : ds.mapIdx (fun i d => d * b ^ i) =
            List.ofFn (fun i : Fin ds.length => ds.get i * b ^ (i : ℕ)) := by
          simpa using (List.mapIdx_eq_ofFn ds (fun i d => d * b ^ i))
        -- finish
        simpa [hleft] using hright.symm
      calc
        L.flatten.sum = (L.map List.sum).sum := hsum_flat
        _ = (ds.mapIdx (fun i d => d * b ^ i)).sum := by
          simpa [hmap_sum]
        _ = Nat.ofDigits b ds := (Nat.ofDigits_eq_sum_mapIdx b ds).symm
        _ = n := by
          simpa [ds] using Nat.ofDigits_digits b n

theorem mem_Ball_A_iff_card_le (n r : ℕ) (m : FreeAbelianMonoid n) :
  m ∈ Ball r (A n) ↔ m.card ≤ r := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hlr, hA, rfl⟩
    have hcard' : ∀ l : List (FreeAbelianMonoid n),
        (∀ x, x ∈ l → x ∈ A n) → (l.sum : Multiset (Fin n)).card = l.length := by
      intro l
      induction l with
      | nil =>
          intro hA
          simp
      | cons a t ih =>
          intro hA
          have ha : a ∈ A n := hA a (by simp)
          have ht : ∀ x, x ∈ t → x ∈ A n := by
            intro x hx
            exact hA x (by simp [hx])
          have iht : (t.sum : Multiset (Fin n)).card = t.length := ih ht
          rcases ha with ⟨i, rfl⟩
          simp [List.sum_cons, Multiset.card_add, iht]
    have hcard : (l.sum : Multiset (Fin n)).card = l.length := hcard' l hA
    simpa [hcard] using hlr
  · intro hmcard
    let ms : Multiset (FreeAbelianMonoid n) := m.map (fun i : Fin n => ({i} : Multiset (Fin n)))
    refine ⟨ms.toList, ?_, ?_, ?_⟩
    · simpa [ms, Multiset.length_toList, Multiset.card_map] using hmcard
    · intro x hx
      have hx' : x ∈ ms := (Multiset.mem_toList.1 hx)
      rcases (Multiset.mem_map.1 hx') with ⟨i, hi, rfl⟩
      simp [A]
    · calc
        ms.toList.sum = ms.sum := by
          simpa using (Multiset.sum_toList ms)
        _ = m := by
          simpa [ms] using (Multiset.sum_map_singleton (s := m))


theorem nat_radius_le_of_real_logbound (n b r s : ℕ) (hb : 2 ≤ b)
  (hs : (s : ℝ) ≥ (n * (b - 1) : ℝ) * ((Real.log r) / (Real.log b) + 1)) :
  n * (b - 1) * (Nat.log b r + 1) ≤ s := by
  classical

  have hb1nat : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb

  -- Step 1: `Nat.log` is bounded by the real logarithm
  have hlog : (Nat.log b r : ℝ) ≤ (Real.log r) / (Real.log b) := by
    have h := Real.natLog_le_logb r b
    have hlogb : Real.logb (b : ℝ) (r : ℝ) = Real.log (r : ℝ) / Real.log (b : ℝ) := by
      simpa using (Real.log_div_log (x := (r : ℝ)) (b := (b : ℝ))).symm
    simpa [hlogb] using h

  have hlog1 : (Nat.log b r : ℝ) + 1 ≤ (Real.log r) / (Real.log b) + 1 := by
    have h' := add_le_add_left hlog (1 : ℝ)
    simpa [add_comm, add_left_comm, add_assoc] using h'

  -- Step 2: multiply by the (nonnegative) factor `n * (b - 1)`
  have hA : 0 ≤ (n : ℝ) * ((b : ℝ) - 1) := by
    have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast hb1nat
    have hbnonneg : 0 ≤ (b : ℝ) - 1 := by
      exact sub_nonneg.mpr hb1
    exact mul_nonneg hn hbnonneg

  have hmul : (n : ℝ) * ((b : ℝ) - 1) * ((Nat.log b r : ℝ) + 1) ≤
      (n : ℝ) * ((b : ℝ) - 1) * ((Real.log r) / (Real.log b) + 1) := by
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hlog1 hA)

  have hs' : (n : ℝ) * ((b : ℝ) - 1) * ((Real.log r) / (Real.log b) + 1) ≤ (s : ℝ) := by
    -- rewrite `hs` from `s ≥ ...`
    -- and rewrite the cast of `b - 1` into a real subtraction
    have hcast_b1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) hb1nat)
    -- start from `hs` and rewrite
    -- `hs` uses `(n * (b - 1) : ℝ)` where the subtraction is in ℝ
    -- so rewrite that as `↑n * ((↑b) - 1)` and then as a cast
    -- to align with our expression
    simpa [mul_assoc, mul_left_comm, mul_comm, hcast_b1, Nat.cast_mul] using hs

  have hreal : (n : ℝ) * ((b : ℝ) - 1) * ((Nat.log b r : ℝ) + 1) ≤ (s : ℝ) :=
    le_trans hmul hs'

  -- Turn the inequality into one about casts of naturals
  have hcast_b1 : (b : ℝ) - 1 = ((b - 1 : ℕ) : ℝ) := by
    simpa using (Nat.cast_sub (R := ℝ) hb1nat).symm

  have hreal' : ((n * (b - 1) * (Nat.log b r + 1) : ℕ) : ℝ) ≤ (s : ℝ) := by
    -- rewrite `hreal` using casts and `hcast_b1`
    -- first, express the left side as a cast of a nat product
    -- `Nat.cast_mul` and `Nat.cast_add` handle the casts
    simpa [hcast_b1, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using hreal

  exact (Nat.cast_le (α := ℝ)).1 hreal'


theorem natlog_le_Dlog2_mul_log (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
  (Nat.log b r + 1 : ℝ) ≤ (Dlog2 : ℝ) * Real.log r := by
  classical
  -- Define the constant C = 2 / log 2
  set C : ℝ := (2 : ℝ) / Real.log 2

  -- C ≤ Dlog2 (as a real) since Dlog2 is the nat ceiling of C
  have hC_le_D : C ≤ (Dlog2 : ℝ) := by
    simpa [C, Dlog2] using (Nat.le_ceil ((2 : ℝ) / Real.log 2))

  -- Monotonicity of Nat.log in the base: b ≥ 2 ⇒ log_b r ≤ log_2 r
  have hlog_nat : Nat.log b r ≤ Nat.log 2 r := by
    have hc : 1 < (2 : ℕ) := by decide
    simpa using (Nat.log_mono (b := b) (c := 2) (m := r) (n := r) hc hb le_rfl)

  -- Lift to reals and add 1
  have hlog1 : (Nat.log b r + 1 : ℝ) ≤ (Nat.log 2 r + 1 : ℝ) := by
    have h' : Nat.log b r + 1 ≤ Nat.log 2 r + 1 := Nat.add_le_add_right hlog_nat 1
    exact_mod_cast h'

  -- Bound (Nat.log 2 r + 1) by C * log r
  have hlog2_bound : (Nat.log 2 r + 1 : ℝ) ≤ C * Real.log r := by
    -- First compare Nat.log with Real.logb
    have hnatlog : (Nat.log 2 r : ℝ) ≤ Real.logb 2 r := by
      simpa using (Real.natLog_le_logb r 2)

    have hnatlog_add : (Nat.log 2 r : ℝ) + 1 ≤ Real.logb 2 r + 1 := by
      -- `add_le_add_left` seems to add on the right in this context
      exact add_le_add_left hnatlog 1

    have hnatlog_add' : (Nat.log 2 r + 1 : ℝ) ≤ Real.logb 2 r + 1 := by
      simpa [Nat.cast_add, Nat.cast_one] using hnatlog_add

    -- Show Real.logb 2 r + 1 ≤ C * log r
    have hlog2pos : 0 < Real.log 2 := by
      simpa using (Real.log_pos (by norm_num : (1 : ℝ) < (2 : ℝ)))
    have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos

    have hlog2_le_logr : Real.log (2 : ℝ) ≤ Real.log (r : ℝ) := by
      have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      exact Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ)) hr'

    have hone_le_div : (1 : ℝ) ≤ Real.log (r : ℝ) / Real.log (2 : ℝ) := by
      have hdiv : Real.log (2 : ℝ) / Real.log (2 : ℝ) ≤ Real.log (r : ℝ) / Real.log (2 : ℝ) := by
        exact div_le_div_of_nonneg_right hlog2_le_logr (le_of_lt hlog2pos)
      simpa [hlog2ne] using hdiv

    have hsum : Real.log (r : ℝ) / Real.log (2 : ℝ) + 1 ≤ 2 * (Real.log (r : ℝ) / Real.log (2 : ℝ)) := by
      linarith [hone_le_div]

    have hmul : 2 * (Real.log (r : ℝ) / Real.log (2 : ℝ)) = C * Real.log (r : ℝ) := by
      simp [C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

    have hlogb_add : Real.logb 2 r + 1 ≤ C * Real.log r := by
      have hlogb_eq : Real.logb (2 : ℝ) (r : ℝ) = Real.log (r : ℝ) / Real.log (2 : ℝ) := by
        simpa using (Real.log_div_log (x := (r : ℝ)) (b := (2 : ℝ))).symm
      have h' : Real.logb (2 : ℝ) (r : ℝ) + 1 ≤ 2 * (Real.log (r : ℝ) / Real.log (2 : ℝ)) := by
        simpa [hlogb_eq] using hsum
      have h'' : Real.logb (2 : ℝ) (r : ℝ) + 1 ≤ C * Real.log (r : ℝ) := by
        simpa [hmul] using h'
      simpa using h''

    exact le_trans hnatlog_add' hlogb_add

  -- Combine with the earlier monotonicity step
  have hC_bound : (Nat.log b r + 1 : ℝ) ≤ C * Real.log r := le_trans hlog1 hlog2_bound

  -- Now C * log r ≤ Dlog2 * log r using C ≤ Dlog2 and log r ≥ 0
  have hlogr_nonneg : 0 ≤ Real.log (r : ℝ) := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
      have : (1 : ℕ) ≤ r := le_trans (by decide : (1 : ℕ) ≤ 2) hr
      exact_mod_cast this
    have hlog1_le : Real.log (1 : ℝ) ≤ Real.log (r : ℝ) := by
      exact Real.log_le_log (by norm_num : (0 : ℝ) < (1 : ℝ)) hr1
    simpa using hlog1_le

  have hmul_le : C * Real.log r ≤ (Dlog2 : ℝ) * Real.log r := by
    exact mul_le_mul_of_nonneg_right hC_le_D (by simpa using hlogr_nonneg)

  exact le_trans hC_bound hmul_le


theorem ncard_Gpow_inter_Ball_le_natlog (n b r : ℕ) (hb : 1 < b) (hr : 2 ≤ r) :
  (Gpow n b ∩ Ball r (A n)).ncard ≤ n * (Nat.log b r + 1) := by
  classical
  let f : Fin n × Fin (Nat.log b r + 1) → FreeAbelianMonoid n := fun p =>
    Multiset.replicate (b ^ (p.2 : ℕ)) p.1
  have hsubset :
      (Gpow n b ∩ Ball r (A n)) ⊆ f '' (Set.univ : Set (Fin n × Fin (Nat.log b r + 1))) := by
    intro m hm
    rcases hm with ⟨hmG, hmB⟩
    rcases hmG with ⟨i, k, rfl⟩
    have hcard : (Multiset.replicate (b ^ k) i).card ≤ r :=
      (mem_Ball_A_iff_card_le n r (Multiset.replicate (b ^ k) i)).1 hmB
    have hbk : b ^ k ≤ r := by
      simpa [Multiset.card_replicate] using hcard
    have hr0 : r ≠ 0 := by
      exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hr)
    have hk : k ≤ Nat.log b r := (Nat.pow_le_iff_le_log hb hr0).1 hbk
    have hklt : k < Nat.log b r + 1 := Nat.lt_succ_of_le hk
    refine ⟨(i, ⟨k, hklt⟩), ?_, ?_⟩
    · trivial
    · simp [f]
  have hfin :
      (f '' (Set.univ : Set (Fin n × Fin (Nat.log b r + 1)))).Finite := by
    exact (Set.finite_univ :
      (Set.univ : Set (Fin n × Fin (Nat.log b r + 1))).Finite).image f
  calc
    (Gpow n b ∩ Ball r (A n)).ncard
        ≤ (f '' (Set.univ : Set (Fin n × Fin (Nat.log b r + 1)))).ncard :=
      Set.ncard_le_ncard hsubset hfin
    _ ≤ (Set.univ : Set (Fin n × Fin (Nat.log b r + 1))).ncard := by
      simpa using
        (Set.ncard_image_le (f := f)
          (s := (Set.univ : Set (Fin n × Fin (Nat.log b r + 1)))))
    _ = Nat.card (Fin n × Fin (Nat.log b r + 1)) := by
      simp [Set.ncard_univ]
    _ = n * (Nat.log b r + 1) := by
      simp [Nat.card_prod, Nat.card_fin]


theorem replicate_mem_Ball_Gpow_of_le (n b r c : ℕ) (hb : 1 < b) (hc : c ≤ r) (i : Fin n) :
  Multiset.replicate c i ∈ Ball ((b - 1) * (Nat.log b r + 1)) (Gpow n b) := by
  classical
  rcases exists_pow_list_sum b c hb with ⟨l, hlpow, hllen, hlsum⟩
  -- build list of multisets
  let l' : List (FreeAbelianMonoid n) := l.map (fun t => Multiset.replicate t i)
  have hl'len : l'.length ≤ (b - 1) * (Nat.log b c + 1) := by
    simpa [l'] using hllen
  have hl'mem : ∀ x, x ∈ l' → x ∈ Gpow n b := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨t, ht, rfl⟩
    rcases hlpow t ht with ⟨k, hk⟩
    refine ⟨i, k, ?_⟩
    simpa [hk]
  have hl'sum : l'.sum = Multiset.replicate c i := by
    have := (Multiset.replicateAddMonoidHom i).map_list_sum l
    -- this : (Multiset.replicateAddMonoidHom i) l.sum = (l.map fun t => replicate t i).sum
    -- rewrite l'
    --
    -- want: l'.sum = replicate c i
    --
    simpa [l', Multiset.replicateAddMonoidHom_apply, hlsum] using this.symm
  -- first show membership in Ball with radius based on c
  have hBallc : Multiset.replicate c i ∈ Ball ((b - 1) * (Nat.log b c + 1)) (Gpow n b) := by
    refine ⟨l', ?_⟩
    refine ⟨hl'len, ?_⟩
    refine ⟨hl'mem, hl'sum⟩
  -- enlarge radius using monotonicity
  have hlog : Nat.log b c ≤ Nat.log b r := by
    exact Nat.log_mono_right (b := b) hc
  have hRS : (b - 1) * (Nat.log b c + 1) ≤ (b - 1) * (Nat.log b r + 1) := by
    have hlog1 : Nat.log b c + 1 ≤ Nat.log b r + 1 := Nat.add_le_add_right hlog 1
    exact Nat.mul_le_mul_left (b - 1) hlog1
  have hsub : Ball ((b - 1) * (Nat.log b c + 1)) (Gpow n b) ⊆ Ball ((b - 1) * (Nat.log b r + 1)) (Gpow n b) := by
    exact Ball_mono_radius n ((b - 1) * (Nat.log b c + 1)) ((b - 1) * (Nat.log b r + 1)) (Gpow n b) hRS
  exact hsub hBallc


theorem Ball_A_subset_Ball_Gpow_natlog (n b r : ℕ) (hb : 1 < b) :
  Ball r (A n) ⊆ Ball (n * (b - 1) * (Nat.log b r + 1)) (Gpow n b) := by
  intro m hm
  classical
  have hcard : m.card ≤ r := (mem_Ball_A_iff_card_le n r m).1 hm
  let k : ℕ := (b - 1) * (Nat.log b r + 1)
  have hterm : ∀ i ∈ m.toFinset, Multiset.replicate (m.count i) i ∈ Ball k (Gpow n b) := by
    intro i hi
    have hc : m.count i ≤ r := le_trans (Multiset.count_le_card i m) hcard
    simpa [k] using (replicate_mem_Ball_Gpow_of_le n b r (m.count i) hb hc i)
  have hsum : (∑ i ∈ m.toFinset, Multiset.replicate (m.count i) i) ∈ Ball (m.toFinset.card * k) (Gpow n b) := by
    apply Ball_sum_finset_mem n (Gpow n b) k m.toFinset (fun i => Multiset.replicate (m.count i) i)
    intro i hi
    exact hterm i hi
  have hdecomp : (∑ i ∈ m.toFinset, Multiset.replicate (m.count i) i) = m := by
    simpa [Multiset.nsmul_singleton] using (Multiset.toFinset_sum_count_nsmul_eq m)
  have hm_ball : m ∈ Ball (m.toFinset.card * k) (Gpow n b) := by
    simpa [hdecomp] using hsum
  have hcard_toFinset : m.toFinset.card ≤ n := by
    simpa using (Finset.card_le_univ (s := m.toFinset) : m.toFinset.card ≤ Fintype.card (Fin n))
  have hle : m.toFinset.card * k ≤ n * k := by
    exact Nat.mul_le_mul_right k hcard_toFinset
  have hm_ball' : m ∈ Ball (n * k) (Gpow n b) := by
    exact (Ball_mono_radius n (m.toFinset.card * k) (n * k) (Gpow n b) hle) hm_ball
  simpa [k, Nat.mul_assoc] using hm_ball'

theorem lemma_1_balls_inclusion (n b : ℕ) (hb : 2 ≤ b) :
  ∃ (G : Set (FreeAbelianMonoid n)) (D : ℕ),
    (∀ (r s : ℕ), (b ^ 2 ≤ r) ∧ (s ≥ n * (b - 1) * ((Real.log r) / (Real.log b) + 1)) →
      (Ball r (A n)) ⊆ (Ball s G)) ∧
    (∀ r : ℕ, 2 ≤ r →
      (G ∩ (Ball r (A n))).ncard ≤ D * n * (Real.log r)) := by
  classical
  refine ⟨Gpow n b, Dlog2, ?_, ?_⟩
  · intro r s hrs
    rcases hrs with ⟨hr, hs⟩
    have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hsub : Ball r (A n) ⊆ Ball (n * (b - 1) * (Nat.log b r + 1)) (Gpow n b) :=
      Ball_A_subset_Ball_Gpow_natlog n b r hb1
    have hNat : n * (b - 1) * (Nat.log b r + 1) ≤ s := by
      have hs' : (s : ℝ) ≥ (n * (b - 1) : ℝ) * ((Real.log r) / (Real.log b) + 1) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hs
      exact nat_radius_le_of_real_logbound n b r s hb hs'
    have hmono :
        Ball (n * (b - 1) * (Nat.log b r + 1)) (Gpow n b) ⊆ Ball s (Gpow n b) :=
      Ball_mono_radius n (n * (b - 1) * (Nat.log b r + 1)) s (Gpow n b) hNat
    exact hsub.trans hmono
  · intro r hr
    have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hnat : (Gpow n b ∩ Ball r (A n)).ncard ≤ n * (Nat.log b r + 1) :=
      ncard_Gpow_inter_Ball_le_natlog n b r hb1 hr
    have hnatR : ((Gpow n b ∩ Ball r (A n)).ncard : ℝ) ≤ (n * (Nat.log b r + 1) : ℝ) := by
      exact_mod_cast hnat
    have hlog : (Nat.log b r + 1 : ℝ) ≤ (Dlog2 : ℝ) * Real.log r :=
      natlog_le_Dlog2_mul_log b r hb hr
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.zero_le n)
    have hmul : (n : ℝ) * (Nat.log b r + 1 : ℝ) ≤ (n : ℝ) * ((Dlog2 : ℝ) * Real.log r) :=
      mul_le_mul_of_nonneg_left hlog hnnonneg
    have hmul' : (n * (Nat.log b r + 1) : ℝ) ≤ (Dlog2 * n * Real.log r) := by
      -- rewrite and use hmul
      --
      simpa [Nat.cast_mul, Nat.cast_add, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact hnatR.trans hmul'


