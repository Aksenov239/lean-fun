import Mathlib

open scoped BigOperators

abbrev FreeAbelianMonoid (n : ℕ) := Multiset (Fin n)

def A (n : ℕ) : Set (FreeAbelianMonoid n) :=
  { {i} | i : Fin n}

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) : Set (FreeAbelianMonoid n) :=
  {m | ∃ l : List (FreeAbelianMonoid n), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

theorem Ball_add {n : ℕ} {X : Set (FreeAbelianMonoid n)} {R S : ℕ} {m1 m2 : FreeAbelianMonoid n} :
  m1 ∈ Ball (n:=n) R X → m2 ∈ Ball (n:=n) S X → (m1 + m2) ∈ Ball (n:=n) (R + S) X := by
  intro hm1 hm2
  rcases hm1 with ⟨l1, hl1len, hl1X, hl1sum⟩
  rcases hm2 with ⟨l2, hl2len, hl2X, hl2sum⟩
  refine ⟨l1 ++ l2, ?_, ?_, ?_⟩
  ·
    simpa [List.length_append] using Nat.add_le_add hl1len hl2len
  ·
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hl1X x hx1
    · exact hl2X x hx2
  ·
    calc
      (l1 ++ l2).sum = l1.sum + l2.sum := by
        simpa using List.sum_append l1 l2
      _ = m1 + m2 := by
        simpa [hl1sum, hl2sum]

theorem Ball_mono_radius {n : ℕ} {X : Set (FreeAbelianMonoid n)} {R S : ℕ} (hRS : R ≤ S) : Ball (n:=n) R X ⊆ Ball (n:=n) S X := by
  intro m hm
  rcases hm with ⟨l, hlR, hlX, hl_sum⟩
  refine ⟨l, ?_, hlX, hl_sum⟩
  exact le_trans hlR hRS


theorem Ball_sum_finset {n : ℕ} {X : Set (FreeAbelianMonoid n)} {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (R : ℕ) (f : ι → FreeAbelianMonoid n) :
  (∀ i ∈ s, f i ∈ Ball (n:=n) R X) →
    (∑ i ∈ s, f i) ∈ Ball (n:=n) (s.card * R) X := by
  classical
  refine Finset.induction_on s ?base ?step
  · intro _
    -- `s = ∅`
    simp [Ball]
  · intro a s ha ih h
    have haBall : f a ∈ Ball (n := n) R X := by
      exact h a (by simp)
    have hsBall : ∀ i ∈ s, f i ∈ Ball (n := n) R X := by
      intro i hi
      exact h i (by simp [hi, ha])
    have hsum_s : (∑ i ∈ s, f i) ∈ Ball (n := n) (s.card * R) X := ih hsBall
    have hsum : (f a + ∑ i ∈ s, f i) ∈ Ball (n := n) (R + s.card * R) X :=
      Ball_add haBall hsum_s
    have hradius : (insert a s).card * R = R + s.card * R := by
      calc
        (insert a s).card * R = (s.card + 1) * R := by
          simpa [Finset.card_insert_of_not_mem ha]
        _ = s.card * R + R := by
          simp [Nat.add_mul]
        _ = R + s.card * R := by
          simpa using Nat.add_comm (s.card * R) R
    -- rewrite the sum and radius into the form handled by `Ball_add`
    rw [Finset.sum_insert ha]
    rw [hradius]
    exact hsum

def Gexp (n b : ℕ) : Set (FreeAbelianMonoid n) :=
  {m | ∃ (i : Fin n) (k : ℕ), m = Multiset.replicate (b ^ k) i}

theorem log_floor_rpow_div_log_le (b : ℕ) (hb : 2 ≤ b) {x : ℝ} (hx : 0 ≤ x) :
  let r : ℕ := ⌊(Real.rpow (b : ℝ) x)⌋₊
  (Real.log r) / (Real.log b) ≤ x := by
  classical
  dsimp
  set y : ℝ := Real.rpow (b : ℝ) x
  set r : ℕ := ⌊y⌋₊

  have hb' : (1 : ℝ) ≤ (b : ℝ) := by
    -- from `2 ≤ b` we get `1 ≤ b`
    exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hb)

  have hy0 : 0 ≤ y := by
    have : (0 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast (Nat.zero_le b)
    simpa [y] using Real.rpow_nonneg this x

  have hy1 : (1 : ℝ) ≤ y := by
    -- `Real.one_le_rpow` : 1 ≤ a → 0 ≤ x → 1 ≤ a^x
    simpa [y] using Real.one_le_rpow hb' hx

  have hrpos : 0 < r := by
    -- `Nat.floor_pos` : 0 < ⌊a⌋₊ ↔ 1 ≤ a
    have : 0 < ⌊y⌋₊ := (Nat.floor_pos).2 hy1
    simpa [r] using this

  have hrle : (r : ℝ) ≤ y := by
    simpa [r] using (Nat.floor_le hy0)

  have hlogle : Real.log (r : ℝ) ≤ Real.log y := by
    -- apply log monotonicity
    have hr0 : (0 : ℝ) < (r : ℝ) := by
      exact_mod_cast hrpos
    exact Real.log_le_log hr0 hrle

  have hbpos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb)

  have hylog : Real.log y = x * Real.log (b : ℝ) := by
    -- `Real.log_rpow` gives `log (a^x) = x * log a`
    -- note the right side is `x * log a` because multiplication is commutative
    simpa [y, mul_comm, mul_left_comm, mul_assoc] using (Real.log_rpow hbpos x)

  have h : Real.log (r : ℝ) ≤ x * Real.log (b : ℝ) := by
    -- combine `hlogle` with the equality for `log y`
    -- rewrite `log y` and use transitivity
    -- `hlogle : log r ≤ log y`
    -- `hylog : log y = x * log b`
    simpa [hylog] using (le_trans hlogle (le_of_eq hylog))

  have hlogbpos : (0 : ℝ) < Real.log (b : ℝ) := by
    have hb1 : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb)
    simpa using Real.log_pos hb1

  -- divide by the positive number `log b`
  have : Real.log (r : ℝ) / Real.log (b : ℝ) ≤ x := by
    -- `div_le_iff₀'` : a / c ≤ b ↔ a ≤ c * b, for c>0
    -- rewrite `x * log b` as `log b * x` to match
    have h' : Real.log (r : ℝ) ≤ Real.log (b : ℝ) * x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    exact (div_le_iff₀' hlogbpos).2 h'

  -- finish
  simpa [r] using this


theorem log_bound_of_r_def (n b s : ℕ) (hb : 2 ≤ b) (hs : s ≥ 3 * n * (b - 1)) :
  let r := Int.toNat <| Int.floor <| Real.rpow (b : ℝ) ((s : ℝ) / (n * (b - 1)) - 1)
  (s : ℝ) ≥ n * (b - 1) * ((Real.log r) / (Real.log b) + 1) := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp
  ·
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have h1b : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1 : 0 < b - 1 := Nat.sub_pos_of_lt h1b

    set denNat : ℕ := n * (b - 1) with hdenNat
    have denNat_pos : 0 < denNat := by
      have : 0 < n * (b - 1) := Nat.mul_pos hnpos hb1
      simpa [hdenNat] using this

    set den : ℝ := (denNat : ℝ) with hden
    have den_pos : 0 < den := by
      have : (0 : ℝ) < (denNat : ℝ) := by
        exact_mod_cast denNat_pos
      simpa [hden] using this

    set x : ℝ := (s : ℝ) / den - 1 with hx

    have hs' : s ≥ 3 * denNat := by
      -- rewrite hs : s ≥ 3 * n * (b-1)
      -- into s ≥ 3 * denNat
      simpa [hdenNat, Nat.mul_assoc] using hs

    have hsR : (3 : ℝ) * den ≤ (s : ℝ) := by
      have hsR' : ((3 * denNat : ℕ) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast hs'
      simpa [hden, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hsR'

    have h3 : (3 : ℝ) ≤ (s : ℝ) / den := by
      exact (le_div_iff₀ den_pos).2 hsR

    have hx0 : 0 ≤ x := by
      -- from h3 : 3 ≤ s/den, get 0 ≤ s/den - 1
      have : (0 : ℝ) ≤ (s : ℝ) / den - 1 := by linarith
      simpa [hx] using this

    have hlog : Real.log (⌊Real.rpow (b : ℝ) x⌋₊) / Real.log b ≤ x := by
      simpa using (log_floor_rpow_div_log_le b hb (x := x) hx0)

    set r0 : ℕ := ⌊Real.rpow (b : ℝ) x⌋₊ with hr0

    have hlog1 : (Real.log r0) / (Real.log b) + 1 ≤ (s : ℝ) / den := by
      -- add 1 to both sides of hlog, then rewrite x
      have : (Real.log r0) / (Real.log b) + 1 ≤ x + 1 := by
        -- from hlog : ... ≤ x
        linarith [hlog]
      -- x + 1 = s/den
      simpa [hx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

    have hmul : den * ((Real.log r0) / (Real.log b) + 1) ≤ (s : ℝ) :=
      (le_div_iff₀' den_pos).1 hlog1

    -- convert den to n*(b-1) and r0 to the r in the statement
    have hb_le : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb

    -- rewrite the goal
    -- unfold the outer let-binding
    dsimp

    -- show the goal by rewriting it to hmul
    -- first, rewrite r in goal to r0
    -- and n*(b-1) to den
    --
    -- We do a big simp using the definitions.
    --
    -- Note: Int.floor_toNat : ⌊a⌋.toNat = ⌊a⌋₊
    -- so it turns Int.toNat (Int.floor _) into ⌊_⌋₊.
    --
    -- We also use Nat.cast_sub hb_le to turn (b-1 : ℕ) into (b : ℝ) - 1.
    --
    -- Finally, we commute/associate multiplications.
    
    -- Convert hmul to the exact goal shape.
    --
    have hmul' : (n : ℝ) * ((b : ℝ) - 1) * ((Real.log (Int.toNat (Int.floor (Real.rpow (b : ℝ) ((s : ℝ) / (n * (b - 1)) - 1)))) ) / (Real.log b) + 1) ≤ (s : ℝ) := by
      -- start from hmul and simp
      --
      -- First rewrite hmul's den to n*(b-1), and r0 to the same floor expression.
      --
      -- r0 is defined as nat floor; relate to Int.floor/toNat using Int.floor_toNat.
      --
      --
      -- We use simp to rewrite x and den.
      --
      --
      simpa [hr0, hx, hden, hdenNat, Nat.cast_mul, Nat.cast_sub hb_le, mul_assoc, mul_left_comm, mul_comm] using hmul

    -- finish: goal is s ≥ ...
    --
    -- turn it into ≤ form
    simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm] using hmul'

theorem mem_ballA_iff_card_le {n : ℕ} {r : ℕ} {m : FreeAbelianMonoid n} : m ∈ Ball (n:=n) r (A n) ↔ m.card ≤ r := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hlr, hlA, rfl⟩
    have hcard : (l.sum).card = l.length := by
      revert hlr hlA
      induction l with
      | nil =>
          intro hlr hlA
          simp
      | cons a l ih =>
          intro hlr hlA
          have ha : a ∈ A n := hlA a (by simp)
          have hlA' : ∀ x, x ∈ l → x ∈ A n := by
            intro x hx
            exact hlA x (by simp [hx])
          have hlr' : l.length ≤ r := by
            exact
              Nat.le_trans (Nat.le_succ l.length) (by simpa using hlr)
          rcases (by simpa [A] using ha) with ⟨i, rfl⟩
          have htail : (l.sum).card = l.length := ih hlr' hlA'
          simp [List.sum_cons, Multiset.card_add, htail]
    simpa [hcard] using hlr
  · intro hmcard
    let ms : Multiset (FreeAbelianMonoid n) :=
      m.map (fun i : Fin n => ({i} : Multiset (Fin n)))
    refine ⟨ms.toList, ?_, ?_, ?_⟩
    · have hlen : ms.toList.length = m.card := by
        calc
          ms.toList.length = ms.card := by
            simpa using (Multiset.length_toList ms)
          _ = m.card := by
            simpa [ms] using
              (Multiset.card_map (fun i : Fin n => ({i} : Multiset (Fin n))) m)
      simpa [hlen] using hmcard
    · intro x hx
      have hxms : x ∈ ms := (Multiset.mem_toList.1 hx)
      rcases (Multiset.mem_map.1 hxms) with ⟨i, hi, rfl⟩
      simp [A]
    · have hsum : ms.sum = m := by
        simpa [ms] using (Multiset.sum_map_singleton m)
      calc
        ms.toList.sum = ms.sum := by
          simpa using (Multiset.sum_toList ms)
        _ = m := hsum

theorem ncard_Gexp_inter_ballA_le_natlog (n b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
  (Gexp n b ∩ Ball (n:=n) r (A n)).ncard ≤ n * (Nat.log b r + 1) := by
  classical
  let f : (Fin n × Fin (Nat.log b r + 1)) → FreeAbelianMonoid n :=
    fun p => Multiset.replicate (b ^ (p.2 : ℕ)) p.1
  have hb' : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb
  have hr0 : r ≠ 0 := by
    have : 0 < r := lt_of_lt_of_le (by decide : 0 < 2) hr
    exact Nat.ne_of_gt this

  have hsubset :
      (Gexp n b ∩ Ball (n:=n) r (A n)) ⊆
        f '' (Set.univ : Set (Fin n × Fin (Nat.log b r + 1))) := by
    intro m hm
    rcases hm with ⟨hmG, hmB⟩
    rcases hmG with ⟨i, k, rfl⟩
    have hkcard : (Multiset.replicate (b ^ k) i).card ≤ r :=
      (mem_ballA_iff_card_le).1 hmB
    have hkpow : b ^ k ≤ r := by
      simpa using hkcard
    have hklog : k ≤ Nat.log b r :=
      (Nat.pow_le_iff_le_log hb' hr0).1 hkpow
    have hklt : k < Nat.log b r + 1 := Nat.lt_succ_of_le hklog
    refine ⟨(i, ⟨k, hklt⟩), ?_, ?_⟩
    · simp
    · simp [f]

  have htfinite :
      (f '' (Set.univ : Set (Fin n × Fin (Nat.log b r + 1)))).Finite :=
    (Set.finite_univ.image f)

  have hle1 :
      (Gexp n b ∩ Ball (n:=n) r (A n)).ncard ≤
        (f '' (Set.univ : Set (Fin n × Fin (Nat.log b r + 1)))).ncard :=
    Set.ncard_le_ncard hsubset htfinite

  have hle2 :
      (f '' (Set.univ : Set (Fin n × Fin (Nat.log b r + 1)))).ncard ≤
        (Set.univ : Set (Fin n × Fin (Nat.log b r + 1))).ncard := by
    simpa using (Set.ncard_image_le (f := f) (s := (Set.univ : Set (Fin n × Fin (Nat.log b r + 1)))))

  calc
    (Gexp n b ∩ Ball (n:=n) r (A n)).ncard
        ≤ (Set.univ : Set (Fin n × Fin (Nat.log b r + 1))).ncard :=
          le_trans hle1 hle2
    _ = Nat.card (Fin n × Fin (Nat.log b r + 1)) := by
          simpa using (Set.ncard_univ (Fin n × Fin (Nat.log b r + 1)))
    _ = n * (Nat.log b r + 1) := by
          simp [Nat.card_prod]

theorem ncard_Gexp_inter_ballA_bound (n b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
  (Gexp n b ∩ Ball (n:=n) r (A n)).ncard ≤ (3 : ℕ) * n * (Real.log r) := by
  classical
  have hnat := ncard_Gexp_inter_ballA_le_natlog n b r hb hr
  have hreal : (↑(Gexp n b ∩ Ball (n:=n) r (A n)).ncard : ℝ) ≤ (↑(n * (Nat.log b r + 1)) : ℝ) := by
    exact_mod_cast hnat
  refine le_trans hreal ?_

  -- Basic real inequalities from the hypotheses
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hb' : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr

  have hlog2pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < (2 : ℝ) := by norm_num
    simpa using Real.log_pos this

  have hlog2_le_logb : Real.log (2 : ℝ) ≤ Real.log (b : ℝ) := by
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.log_le_log h2pos hb'

  have hlog2_le_logr : Real.log (2 : ℝ) ≤ Real.log (r : ℝ) := by
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.log_le_log h2pos hr'

  have hlogr_nonneg : 0 ≤ Real.log (r : ℝ) := le_trans (le_of_lt hlog2pos) hlog2_le_logr

  have hdiv_le : Real.log (r : ℝ) / Real.log (b : ℝ) ≤ Real.log (r : ℝ) / Real.log (2 : ℝ) := by
    exact div_le_div_of_nonneg_left hlogr_nonneg hlog2pos hlog2_le_logb

  -- Nat.log bound
  have hnatlog_le_div : (Nat.log b r : ℝ) ≤ Real.log (r : ℝ) / Real.log (b : ℝ) := by
    have h := (Real.natLog_le_logb r b)
    have hlogb_eq : Real.logb (b : ℝ) (r : ℝ) = Real.log (r : ℝ) / Real.log (b : ℝ) := by
      simpa using (Real.log_div_log (b := (b : ℝ)) (x := (r : ℝ))).symm
    simpa [hlogb_eq] using h

  have hnatlog_le_div2 : (Nat.log b r : ℝ) ≤ Real.log (r : ℝ) / Real.log (2 : ℝ) :=
    le_trans hnatlog_le_div hdiv_le

  have h1_le_div2 : (1 : ℝ) ≤ Real.log (r : ℝ) / Real.log (2 : ℝ) := by
    -- 1 ≤ log r / log 2 because log 2 ≤ log r and log 2 > 0
    exact (one_le_div hlog2pos).2 hlog2_le_logr

  have hlog_add_one : (Nat.log b r : ℝ) + 1 ≤ (2 : ℝ) * (Real.log (r : ℝ) / Real.log (2 : ℝ)) := by
    have hadd : (Nat.log b r : ℝ) + 1 ≤ (Real.log (r : ℝ) / Real.log (2 : ℝ)) + (Real.log (r : ℝ) / Real.log (2 : ℝ)) :=
      add_le_add hnatlog_le_div2 h1_le_div2
    -- simplify
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hadd

  -- crude numerical bound: 2 / log 2 < 3
  have htwo_div_log2_le_three : (2 : ℝ) / Real.log (2 : ℝ) ≤ (3 : ℝ) := by
    have hlog2_gt : (0.6931471803 : ℝ) < Real.log (2 : ℝ) := by
      simpa using Real.log_two_gt_d9
    have hpos_d9 : 0 < (0.6931471803 : ℝ) := by norm_num
    have hdiv_lt : (2 : ℝ) / Real.log (2 : ℝ) < (2 : ℝ) / (0.6931471803 : ℝ) := by
      -- larger denominator gives smaller quotient
      simpa [div_eq_mul_inv] using (div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < (2 : ℝ)) hpos_d9 hlog2_gt)
    have hdiv2_lt_three : (2 : ℝ) / (0.6931471803 : ℝ) < (3 : ℝ) := by
      norm_num
    exact le_of_lt (lt_trans hdiv_lt hdiv2_lt_three)

  have htwo_mul_div2_le : (2 : ℝ) * (Real.log (r : ℝ) / Real.log (2 : ℝ)) ≤ (3 : ℝ) * Real.log (r : ℝ) := by
    -- rewrite and use the constant bound
    -- (2 * (log r / log2)) = (2 / log2) * log r
    have hrewrite : (2 : ℝ) * (Real.log (r : ℝ) / Real.log (2 : ℝ)) = ((2 : ℝ) / Real.log (2 : ℝ)) * Real.log (r : ℝ) := by
      ring
    -- apply `mul_le_mul_of_nonneg_right`
    have := mul_le_mul_of_nonneg_right htwo_div_log2_le_three hlogr_nonneg
    -- now rewrite
    simpa [hrewrite, mul_assoc, mul_left_comm, mul_comm] using this

  have hlog_add_one' : (Nat.log b r : ℝ) + 1 ≤ (3 : ℝ) * Real.log (r : ℝ) :=
    le_trans hlog_add_one htwo_mul_div2_le

  -- cast (Nat.log b r + 1) to ℝ and conclude
  have hlog_nat_add_one : (↑(Nat.log b r + 1) : ℝ) ≤ (3 : ℝ) * Real.log (r : ℝ) := by
    -- `Nat.cast_add` turns this into (Nat.log : ℝ) + 1
    simpa using hlog_add_one'

  -- multiply by n ≥ 0
  have hn_mul : (↑(n * (Nat.log b r + 1)) : ℝ) ≤ (n : ℝ) * ((3 : ℝ) * Real.log (r : ℝ)) := by
    -- first rewrite the LHS as n * (Nat.log+1)
    have hmul : (↑(n * (Nat.log b r + 1)) : ℝ) = (n : ℝ) * (↑(Nat.log b r + 1) : ℝ) := by
      norm_cast
    -- use monotonicity
    have := mul_le_mul_of_nonneg_left hlog_nat_add_one hn0
    -- rewrite
    simpa [hmul, mul_assoc] using this

  -- finish by rearranging multiplications
  -- RHS goal is ↑3 * ↑n * log r
  -- Our bound is n * (3 * log r)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hn_mul

theorem replicate_mem_ball_Gexp_natlog (n b c : ℕ) (hb : 2 ≤ b) (i : Fin n) :
  Multiset.replicate c i ∈ Ball (n:=n) ((b - 1) * (Nat.log b c + 1)) (Gexp n b) := by
  classical
  by_cases hc0 : c = 0
  · subst hc0
    refine ⟨[], ?_, ?_, ?_⟩
    · simp [Ball]
    · intro x hx
      cases hx
    · simp [Ball]
  · have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1:ℕ) < 2) hb
    let digits : List ℕ := Nat.digits b c
    let chunk (k : ℕ) : FreeAbelianMonoid n := Multiset.replicate (b ^ k) i
    let build : List ℕ → ℕ → List (FreeAbelianMonoid n) :=
      fun ds =>
        ds.recOn (motive := fun _ => ℕ → List (FreeAbelianMonoid n))
          (fun _k => [])
          (fun d ds ih k => List.replicate d (chunk k) ++ ih (k + 1))
    let l : List (FreeAbelianMonoid n) := build digits 0

    have hmem_build : ∀ (ds : List ℕ) (k : ℕ) {x : FreeAbelianMonoid n}, x ∈ build ds k → x ∈ Gexp n b := by
      intro ds
      induction ds with
      | nil =>
          intro k x hx
          simp [build] at hx
      | cons d ds ih =>
          intro k x hx
          have hx' : x ∈ List.replicate d (chunk k) ++ build ds (k + 1) := by
            simpa [build] using hx
          rcases List.mem_append.1 hx' with hx1 | hx2
          · have hx_single : x ∈ [chunk k] :=
              (List.replicate_subset_singleton d (chunk k)) hx1
            have hx_eq : x = chunk k := by
              simpa using hx_single
            subst hx_eq
            refine ⟨i, k, ?_⟩
            simp [chunk]
          · exact ih (k := k + 1) hx2

    have hsum_build : ∀ (ds : List ℕ) (k : ℕ), (build ds k).sum = Multiset.replicate (b ^ k * Nat.ofDigits b ds) i := by
      intro ds
      induction ds with
      | nil =>
          intro k
          simp [build]
      | cons d ds ih =>
          intro k
          simp [build, List.sum_append, List.sum_replicate, ih, chunk, Nat.ofDigits_cons,
            Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Multiset.replicate_add,
            Multiset.nsmul_replicate]

    refine ⟨l, ?_, ?_, ?_⟩
    · -- length bound
      have hlen_build : ∀ (ds : List ℕ) (k : ℕ), (build ds k).length = ds.sum := by
        intro ds
        induction ds with
        | nil =>
            intro k
            simp [build]
        | cons d ds ih =>
            intro k
            simp [build, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hlen_l : l.length = digits.sum := by
        simpa [l] using (hlen_build digits 0)
      have hsum_digits : digits.sum ≤ digits.length * (b - 1) := by
        -- bound each digit by `b-1`
        refine (List.sum_le_card_nsmul (l := digits) (n := (b - 1)) ?_)
        intro d hd
        have hd' : d ∈ Nat.digits b c := by
          simpa [digits] using hd
        have hdlt : d < b := Nat.digits_lt_base (b := b) (m := c) hb1 hd'
        exact Nat.le_pred_of_lt hdlt
      have hlen_digits : digits.length = Nat.log b c + 1 := by
        simpa [digits] using (Nat.digits_len b c hb1 hc0)
      have hsum_digits' : digits.sum ≤ (Nat.log b c + 1) * (b - 1) := by
        simpa [hlen_digits] using hsum_digits
      have hsum_digits'' : digits.sum ≤ (b - 1) * (Nat.log b c + 1) := by
        simpa [Nat.mul_comm] using hsum_digits'
      simpa [hlen_l] using hsum_digits''
    · intro x hx
      exact hmem_build digits 0 hx
    · -- sum computation
      have hl : l.sum = Multiset.replicate (Nat.ofDigits b digits) i := by
        simpa [l, pow_zero] using (hsum_build digits 0)
      have hdigits : Nat.ofDigits b digits = c := by
        simpa [digits] using (Nat.ofDigits_digits b c)
      simpa [hdigits] using hl

theorem sum_replicate_count_eq {n : ℕ} (m : FreeAbelianMonoid n) :
  (∑ i : Fin n, Multiset.replicate (m.count i) i) = m := by
  classical
  ext a
  -- compare multiplicities
  -- count on the LHS
  calc
    Multiset.count a (∑ i : Fin n, Multiset.replicate (m.count i) i)
        = ∑ i : Fin n, Multiset.count a (Multiset.replicate (m.count i) i) := by
          -- rewrite count of a sum as sum of counts
          simpa using
            (Multiset.count_sum' (s := (Finset.univ : Finset (Fin n))) (a := a)
              (f := fun i : Fin n => Multiset.replicate (m.count i) i))
    _ = ∑ i : Fin n, (if i = a then m.count i else 0) := by
          -- compute multiplicity in each replicated multiset
          simp [Multiset.count_replicate]
    _ = m.count a := by
          -- only the term `i = a` contributes
          simpa using
            (Finset.sum_ite_eq (s := (Finset.univ : Finset (Fin n))) (a := a)
              (f := fun i : Fin n => m.count i))

theorem ballA_subset_ballGexp_natlog (n b r : ℕ) (hb : 2 ≤ b) : Ball (n:=n) r (A n) ⊆ Ball (n:=n) (n * (b - 1) * (Nat.log b r + 1)) (Gexp n b) := by
  intro m hm
  classical
  have hcard : m.card ≤ r := (mem_ballA_iff_card_le (n:=n) (r:=r) (m:=m)).1 hm

  -- uniform radius
  let R : ℕ := (b - 1) * (Nat.log b r + 1)

  have hcoord : ∀ i : Fin n, Multiset.replicate (m.count i) i ∈ Ball (n:=n) R (Gexp n b) := by
    intro i
    -- coordinate-specific ball membership
    have h0 : Multiset.replicate (m.count i) i ∈
        Ball (n:=n) ((b - 1) * (Nat.log b (m.count i) + 1)) (Gexp n b) := by
      simpa using (replicate_mem_ball_Gexp_natlog (n := n) (b := b) (c := m.count i) hb i)
    -- show the coordinate radius is ≤ the uniform radius R
    have hcount : m.count i ≤ r := le_trans (Multiset.count_le_card i m) hcard
    have hlog : Nat.log b (m.count i) ≤ Nat.log b r := Nat.log_mono_right (b := b) hcount
    have hrad : (b - 1) * (Nat.log b (m.count i) + 1) ≤ R := by
      dsimp [R]
      exact Nat.mul_le_mul_left (b - 1) (Nat.add_le_add_right hlog 1)
    exact (Ball_mono_radius (n:=n) (X:=Gexp n b) hrad) h0

  -- sum the coordinates
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin n)), Multiset.replicate (m.count i) i) ∈
      Ball (n:=n) ((Finset.univ : Finset (Fin n)).card * R) (Gexp n b) := by
    refine Ball_sum_finset (n:=n) (X:=Gexp n b) (s := (Finset.univ : Finset (Fin n))) R
        (fun i => Multiset.replicate (m.count i) i) ?_
    intro i hi
    simpa using hcoord i

  -- convert to the `Fintype`-sum and simplify the radius
  have hsum' : (∑ i : Fin n, Multiset.replicate (m.count i) i) ∈
      Ball (n:=n) (n * (b - 1) * (Nat.log b r + 1)) (Gexp n b) := by
    -- `∑ i : Fin n` is definitionaly `∑ i ∈ Finset.univ`
    have hsum'' : (∑ i : Fin n, Multiset.replicate (m.count i) i) ∈
        Ball (n:=n) ((Finset.univ : Finset (Fin n)).card * R) (Gexp n b) := by
      simpa using hsum
    have hcarduniv : ((Finset.univ : Finset (Fin n)).card) = n := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_univ : ((Finset.univ : Finset (Fin n)).card) = Fintype.card (Fin n))
    simpa [R, hcarduniv, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum''

  -- finish by rewriting the sum to m
  simpa [sum_replicate_count_eq (n:=n) m] using hsum'

theorem ballA_subset_ballGexp_of_log (n b r s : ℕ) (hb : 2 ≤ b)
  (hs : (s : ℝ) ≥ n * (b - 1) * ((Real.log r) / (Real.log b) + 1)) :
  Ball (n:=n) r (A n) ⊆ Ball (n:=n) s (Gexp n b) := by
  classical
  have hb1 : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hlog : (Nat.log b r : ℝ) ≤ (Real.log r) / (Real.log b) := by
    have h := (Real.natLog_le_logb r b)
    simpa [Real.log_div_log] using h
  have hlog1 : (Nat.log b r + 1 : ℝ) ≤ (Real.log r) / (Real.log b) + 1 := by
    linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hb0 : (0 : ℝ) ≤ (b : ℝ) - 1 := by
    have hb' : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    linarith
  have hcoeff : (0 : ℝ) ≤ (n : ℝ) * ((b : ℝ) - 1) := mul_nonneg hn0 hb0
  have hcoeff' : (0 : ℝ) ≤ (n * (b - 1) : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_sub hb1, mul_assoc, mul_left_comm, mul_comm] using hcoeff
  have hmul : (n * (b - 1) : ℝ) * (Nat.log b r + 1) ≤
      (n * (b - 1) : ℝ) * ((Real.log r) / (Real.log b) + 1) := by
    exact mul_le_mul_of_nonneg_left hlog1 hcoeff'
  -- hs bounds the RHS by s
  have hs0 : (n * (b - 1) : ℝ) * ((Real.log r) / (Real.log b) + 1) ≤ (s : ℝ) := by
    simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm] using hs
  have hrad_exp : (n * (b - 1) : ℝ) * (Nat.log b r + 1) ≤ (s : ℝ) :=
    le_trans hmul hs0
  -- rewrite into a cast of the nat expression
  have hrad_cast : ((n * (b - 1) * (Nat.log b r + 1) : ℕ) : ℝ) ≤ (s : ℝ) := by
    -- expand the casted nat expression and match `hrad_exp`
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hb1, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hrad_exp
  -- convert back to nat
  have hrad_nat : n * (b - 1) * (Nat.log b r + 1) ≤ s := (Nat.cast_le (α := ℝ)).1 hrad_cast
  -- Now finish the main goal using radius monotonicity.
  have h₁ := ballA_subset_ballGexp_natlog n b r hb
  have h₂ := Ball_mono_radius (n:=n) (X:=Gexp n b)
    (R:=n * (b - 1) * (Nat.log b r + 1)) (S:=s) hrad_nat
  exact Set.Subset.trans h₁ h₂

theorem theorem_1_exponential_expansion (n b : ℕ)
  (hb : 2 ≤ b) :
  ∃ (G : Set (FreeAbelianMonoid n)) (D : ℕ),
    (∀ s : ℕ, (s ≥ 3 * n * (b - 1)) →
      let r := Int.toNat <| Int.floor <| Real.rpow (b : ℝ) ((s : ℝ) / (n * (b - 1)) - 1)
      (Ball (n:=n) r (A n) ⊆ (Ball (n:=n) s G))) ∧
    (∀ r : ℕ, 2 ≤ r →
      (G ∩ (Ball (n:=n) r (A n))).ncard ≤ D * n * (Real.log r)) := by
  classical
  refine ⟨Gexp n b, 3, ?_, ?_⟩
  · intro s hs
    -- unfold the `let r := ...` in the goal
    simp only
    -- after simp, the goal is about the explicit `r` expression
    have hslog : (s : ℝ) ≥ n * (b - 1) * ((Real.log (Int.toNat <| Int.floor <| Real.rpow (b : ℝ)
        ((s : ℝ) / (n * (b - 1)) - 1))) / (Real.log b) + 1) := by
      simpa using (log_bound_of_r_def n b s hb hs)
    exact
      ballA_subset_ballGexp_of_log n b
        (Int.toNat <| Int.floor <| Real.rpow (b : ℝ) ((s : ℝ) / (n * (b - 1)) - 1))
        s hb hslog
  · intro r hr
    simpa using (ncard_Gexp_inter_ballA_bound n b r hb hr)


