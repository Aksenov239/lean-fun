import Mathlib


open scoped BigOperators

namespace abelian

abbrev FreeAbelianMonoid (n : ℕ) := Multiset (Fin n)

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) : Set (FreeAbelianMonoid n) :=
  {m | ∃ l : List (FreeAbelianMonoid n), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

def A (n : ℕ) : Set (FreeAbelianMonoid n) :=
  { {i} | i : Fin n}

theorem lemma_1_balls_inclusion
  (n b : ℕ)
  (hb : 2 ≤ b) :
  ∃ (G : Set (FreeAbelianMonoid n)) (D : ℕ),
    (∀ (r s : ℕ), (b ^ 2 ≤ r) ∧ (s ≥ n * (b - 1) * ((Real.log r) / (Real.log b) + 1)) →
      (Ball r (A n)) ⊆ (Ball s G)) ∧
    (∀ r : ℕ, 2 ≤ r →
      (G ∩ (Ball r (A n))).ncard ≤ D * n * (Real.log r)) :=
  sorry

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
    (∃ (K : ℕ), ∀ (s : ℕ), (s ≥ 2) →
      let r := Int.toNat <| Int.floor <| Real.exp (K * s * (Real.log s))
      Ball r (A n) ⊆ Ball s (G ∪ (A n))) :=
    sorry

def isWarring (k : ℕ) (n : ℕ) : Prop :=
  ∀ x : ℕ, ∃ l : List ℕ, l.length ≤ n ∧ (l.map (fun (y : ℕ) => y ^ k)).sum = x

theorem theorem_3_polynomial_density
  (n k : ℕ) (hk : k ≥ 2) :
  ∃ (G : Set (FreeAbelianMonoid n)),
    (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ n * (Real.rpow r ((1 : ℝ) / k))) ∧
    (∀ (g : ℕ), (isWarring k g) → (∀ (r : ℕ), (Ball r (A n)) ⊆ (Ball (n * g) (G ∪ (A n))))) :=
    sorry

end abelian

namespace free

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeMonoid (Fin n))) : Set (FreeMonoid (Fin n)) :=
  {m | ∃ l : List (FreeMonoid (Fin n)), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.prod = m}

def A (n : ℕ) : Set (FreeMonoid (Fin n)) :=
  { [i] | i : Fin n}

theorem theorem_4_logarithmic_density_simple
  (n : ℕ) (hn : n ≥ 2)
  (G : Set (FreeMonoid (Fin n)))
  (c : ℕ)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c)) :
    ∃ (d : ℕ), ∀ (s : ℕ), ¬ (Ball (d * s) (A n) ⊆ Ball s (G ∪ (A n))) :=
    sorry

theorem theorem_4_logarithmic_density
  (n : ℕ) (hn : n ≥ 2)
  (G : Set (FreeMonoid (Fin n)))
  (c : ℕ)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c)) :
    let d := Int.toNat <|
              max 2 (Int.ceil (2 * (Real.log (2 * (Real.exp 1) * (n + c))) / (Real.log n)))
    ∀ (s : ℕ), ¬ (Ball (d * s) (A n) ⊆ Ball s (G ∪ (A n))) :=
  sorry

def isGoodDLemma5 (n : ℕ) (c p : ℝ) (d : ℕ) : Prop :=
  (d ≥ 3) ∧ (Real.rpow n d > 4 * (Real.exp 1) * (n + c) * (Real.rpow d (p + 1)))

end free


open scoped BigOperators

def A (n : ℕ) : Set (FreeMonoid (Fin n)) :=
  { [i] | i : Fin n}

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeMonoid (Fin n))) : Set (FreeMonoid (Fin n)) :=
  {m | ∃ l : List (FreeMonoid (Fin n)), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.prod = m}

theorem Ball_exists_rep_pos_lengths (n : ℕ) (X : Set (FreeMonoid (Fin n))) (s : ℕ) (w : FreeMonoid (Fin n)) :
  w ∈ Ball s X →
    ∃ l : List (FreeMonoid (Fin n)),
      l.length ≤ s ∧ (∀ x, x ∈ l → x ∈ X) ∧ (∀ x, x ∈ l → 1 ≤ x.length) ∧ l.prod = w := by
  intro hw
  rcases hw with ⟨l, hl_len, hlX, hlprod⟩
  classical
  let f : FreeMonoid (Fin n) → Bool := fun x => !decide (x = (1 : FreeMonoid (Fin n)))
  let l' : List (FreeMonoid (Fin n)) := l.filter f
  refine ⟨l', ?_, ?_, ?_, ?_⟩
  ·
    have hlen' : l'.length ≤ l.length := by
      have h := (List.length_eq_length_filter_add (l := l) f)
      have : (l.filter f).length ≤ (l.filter f).length + (l.filter (!f ·)).length :=
        Nat.le_add_right _ _
      simpa [l', h.symm] using this
    exact le_trans hlen' hl_len
  ·
    intro x hx
    have hx0 : x ∈ l.filter f := by
      simpa [l'] using hx
    have hx' : x ∈ l := (List.mem_filter.1 hx0).1
    exact hlX x hx'
  ·
    intro x hx
    have hx0 : x ∈ l.filter f := by
      simpa [l'] using hx
    have hx_pred : f x = true := (List.mem_filter.1 hx0).2
    have hx_dec : decide (x = (1 : FreeMonoid (Fin n))) = false := by
      simpa [f] using hx_pred
    have hx_ne1 : x ≠ (1 : FreeMonoid (Fin n)) :=
      (Bool.decide_false_iff (p := x = (1 : FreeMonoid (Fin n)))).1 hx_dec
    have hx_len_ne0 : x.length ≠ 0 := by
      intro hx0'
      apply hx_ne1
      exact (FreeMonoid.length_eq_zero).1 hx0'
    have hx_pos : 0 < x.length := Nat.pos_of_ne_zero hx_len_ne0
    exact Nat.succ_le_of_lt hx_pos
  ·
    have hprod' : ∀ l : List (FreeMonoid (Fin n)), (l.filter f).prod = l.prod := by
      intro l
      induction l with
      | nil =>
          simp
      | cons a t ih =>
          by_cases ha : a = (1 : FreeMonoid (Fin n))
          · subst ha
            simp [f, ih]
          · simp [f, ha, ih]
    have hprod : l'.prod = l.prod := by
      simpa [l'] using hprod' l
    calc
      l'.prod = l.prod := hprod
      _ = w := hlprod

theorem choose_ds_le_ed_pow (d s : ℕ) : (Nat.choose (d * s) s : ℝ) ≤ (Real.exp 1 * d) ^ s := by
  classical
  -- Start from the standard bound `choose ≤ n^k / k!`.
  have hchoose : (Nat.choose (d * s) s : ℝ) ≤ ((d * s : ℝ) ^ s) / (Nat.factorial s) := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) s (d * s))

  -- Bound the factorial term using the exponential series.
  have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast (Nat.zero_le s)
  have hpowfac : ( (s : ℝ) ^ s) / (Nat.factorial s) ≤ Real.exp (s : ℝ) := by
    simpa using (Real.pow_div_factorial_le_exp (x := (s : ℝ)) hsnonneg s)

  calc
    (Nat.choose (d * s) s : ℝ)
        ≤ ((d * s : ℝ) ^ s) / (Nat.factorial s) := hchoose
    _ = ((d : ℝ) ^ s * (s : ℝ) ^ s) / (Nat.factorial s) := by
          -- cast `d*s` to ℝ and expand the power
          simp [Nat.cast_mul, mul_pow]
    _ = (d : ℝ) ^ s * ((s : ℝ) ^ s / (Nat.factorial s)) := by
          -- factor out `(d:ℝ)^s` using `(a*b)/c = a*(b/c)`
          simpa [mul_assoc] using
            (mul_div_assoc ((d : ℝ) ^ s) ((s : ℝ) ^ s) (Nat.factorial s : ℝ))
    _ ≤ (d : ℝ) ^ s * Real.exp (s : ℝ) := by
          -- multiply `hpowfac` by the nonnegative factor `(d:ℝ)^s`
          have hdnonneg : (0 : ℝ) ≤ (d : ℝ) ^ s := by
            positivity
          exact mul_le_mul_of_nonneg_left hpowfac hdnonneg
    _ = (Real.exp 1) ^ s * (d : ℝ) ^ s := by
          have hexp : Real.exp (s : ℝ) = (Real.exp 1) ^ s := by
            simpa [mul_one] using (Real.exp_nat_mul (x := (1 : ℝ)) (n := s))
          -- rewrite `exp s` and commute the product
          calc
            (d : ℝ) ^ s * Real.exp (s : ℝ)
                = (d : ℝ) ^ s * (Real.exp 1) ^ s := by
                    -- rewrite `exp (s:ℝ)`
                    rw [hexp]
            _ = (Real.exp 1) ^ s * (d : ℝ) ^ s := by
                    simpa using (mul_comm ((d : ℝ) ^ s) ((Real.exp 1) ^ s))
    _ = (Real.exp 1 * d) ^ s := by
          -- combine as a single power
          simpa using (mul_pow (Real.exp 1) (d : ℝ) s).symm


theorem choose_mono_second_of_le_half (n r t : ℕ) (ht : r + t ≤ n / 2) : Nat.choose n r ≤ Nat.choose n (r + t) := by
  revert ht
  induction t with
  | zero =>
      intro ht
      simp
  | succ t ih =>
      intro ht
      have ht' : r + t ≤ n / 2 := by
        have hrt : r + t ≤ r + Nat.succ t :=
          Nat.add_le_add_left (Nat.le_succ t) r
        exact le_trans hrt ht
      have ih' : Nat.choose n r ≤ Nat.choose n (r + t) := ih ht'
      have hlt : r + t < n / 2 := by
        have ht_succ : Nat.succ (r + t) ≤ n / 2 := by
          have ht' := ht
          rw [Nat.add_succ] at ht'
          exact ht'
        exact Nat.lt_of_succ_le ht_succ
      have hstep : Nat.choose n (r + t) ≤ Nat.choose n (r + t + 1) :=
        Nat.choose_le_succ_of_lt_half_left (r := r + t) (n := n) hlt
      have goal' : Nat.choose n r ≤ Nat.choose n (r + t + 1) := le_trans ih' hstep
      rw [Nat.add_succ, Nat.succ_eq_add_one]
      exact goal'

theorem choose_ds_pred_k_pred_le_choose_ds_s (d s k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) (hd : 2 ≤ d) :
  Nat.choose (d * s - 1) (k - 1) ≤ Nat.choose (d * s) s := by
  classical
  set n : ℕ := d * s
  have hs1 : 1 ≤ s := le_trans hk hks
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_two hd
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one hs1
  have hnpos : 0 < n := by
    simpa [n] using Nat.mul_pos hdpos hspos

  have hs_half : s - 1 ≤ (n - 1) / 2 := by
    have h2s_le_n : 2 * s ≤ n := by
      simpa [n, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.mul_le_mul_right s hd)
    have h2s1_le_n1 : 2 * s - 1 ≤ n - 1 := by
      exact Nat.sub_le_sub_right h2s_le_n 1
    have h2sm2_le_h2sm1 : 2 * s - 2 ≤ 2 * s - 1 := by
      simpa using (tsub_le_tsub_left (by decide : (1 : ℕ) ≤ 2) (2 * s))
    have h2sm2_le_n1 : 2 * s - 2 ≤ n - 1 := le_trans h2sm2_le_h2sm1 h2s1_le_n1
    have hmul_nat : 2 * (s - 1) ≤ n - 1 := by
      simpa [mul_tsub_one] using h2sm2_le_n1
    -- Cast to ℤ in the precise form needed by `Nat.le_div_two_iff_mul_two_le`
    have hmul_int : (↑(s - 1) : ℤ) * 2 ≤ (↑(n - 1) : ℤ) := by
      have hmul_int' : (↑(2 * (s - 1)) : ℤ) ≤ (↑(n - 1) : ℤ) := by
        exact_mod_cast hmul_nat
      -- rewrite `↑(2*(s-1))` as `↑(s-1)*2`
      simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hmul_int'
    exact (Nat.le_div_two_iff_mul_two_le (n := n - 1) (m := s - 1)).2 (by
      simpa using hmul_int)

  have hk1s1 : k - 1 ≤ s - 1 := by
    exact Nat.sub_le_sub_right hks 1

  have hchoose1 : Nat.choose (n - 1) (k - 1) ≤ Nat.choose (n - 1) (s - 1) := by
    have ht : (k - 1) + ((s - 1) - (k - 1)) ≤ (n - 1) / 2 := by
      simpa [add_tsub_cancel_of_le hk1s1] using hs_half
    have hmono :=
      choose_mono_second_of_le_half (n := n - 1) (r := k - 1) (t := (s - 1) - (k - 1)) ht
    simpa [add_tsub_cancel_of_le hk1s1] using hmono

  have hchoose2 : Nat.choose (n - 1) (s - 1) ≤ Nat.choose n s := by
    have hpascal : Nat.choose n ((s - 1) + 1) = Nat.choose (n - 1) (s - 1) + Nat.choose (n - 1) ((s - 1) + 1) := by
      simpa using Nat.choose_succ_right n (s - 1) hnpos
    have hs_succ : (s - 1) + 1 = s := Nat.sub_add_cancel hs1
    have hpascal' : Nat.choose n s = Nat.choose (n - 1) (s - 1) + Nat.choose (n - 1) s := by
      simpa [hs_succ] using hpascal
    simpa [hpascal'] using (Nat.le_add_right (Nat.choose (n - 1) (s - 1)) (Nat.choose (n - 1) s))

  have hmain : Nat.choose (n - 1) (k - 1) ≤ Nat.choose n s := le_trans hchoose1 hchoose2
  simpa [n] using hmain

theorem compositionAsSetEquiv_card_eq_length_pred (r : ℕ) (c : CompositionAsSet r) (hr : 0 < r) :
  (compositionAsSetEquiv r c).card = c.length - 1 := by
  classical
  -- Let `s` be the finset of internal boundaries associated to `c`.
  let s : Finset (Fin (r - 1)) := compositionAsSetEquiv r c
  -- The embedding `j ↦ j+1` from `Fin (r-1)` to `Fin (r+1)`.
  let f : Fin (r - 1) ↪ Fin r.succ :=
    ⟨fun j => ⟨(j : ℕ) + 1, by
        have hj : (j : ℕ) < r - 1 := j.2
        lia⟩,
      by
        intro a b hab
        apply Fin.ext
        have h : (a : ℕ) + 1 = (b : ℕ) + 1 := by
          simpa using congrArg Fin.val hab
        exact Nat.succ_injective (by simpa [Nat.succ_eq_add_one] using h)⟩
  let t : Finset (Fin r.succ) := s.map f

  -- Describe the boundary set of the inverse explicitly as `{0, last} ∪ image (j ↦ j+1)`.
  have hbound : ((compositionAsSetEquiv r).symm s).boundaries =
      insert (0 : Fin r.succ) (insert (Fin.last r) t) := by
    ext i
    constructor
    · intro hi
      have hi' : i = 0 ∨ i = Fin.last r ∨ ∃ j : Fin (r - 1), j ∈ s ∧ (i : ℕ) = j + 1 := by
        simpa [compositionAsSetEquiv, exists_prop] using hi
      rcases hi' with h0 | hlast | ⟨j, hj, hij⟩
      · simp [h0]
      · simp [hlast]
      · have : (f j : Fin r.succ) = i := by
          apply Fin.ext
          simpa [f] using hij.symm
        have : i ∈ t := by
          refine Finset.mem_map.2 ?_
          refine ⟨j, hj, ?_⟩
          simpa [t] using this
        simp [t, this]
    · intro hi
      have hi' : i = 0 ∨ i = Fin.last r ∨ i ∈ t := by
        simpa [Finset.mem_insert, Finset.mem_map, t] using hi
      rcases hi' with h0 | hlast | ht
      · subst h0
        simp [compositionAsSetEquiv]
      · subst hlast
        simp [compositionAsSetEquiv]
      · rcases Finset.mem_map.1 (by simpa [t] using ht) with ⟨j, hj, hjf⟩
        have hij : (i : ℕ) = j + 1 := by
          have hval : (f j : ℕ) = i := congrArg Fin.val hjf
          simpa [f] using hval.symm
        have : i = 0 ∨ i = Fin.last r ∨ ∃ j : Fin (r - 1), j ∈ s ∧ (i : ℕ) = j + 1 :=
          Or.inr (Or.inr ⟨j, hj, hij⟩)
        simpa [compositionAsSetEquiv, exists_prop] using this

  have htcard : t.card = s.card := by
    simpa [t] using (Finset.card_map f s)

  have h0last : (0 : Fin r.succ) ≠ Fin.last r := by
    intro h
    have hval : (0 : ℕ) = r := by
      simpa using congrArg Fin.val h
    exact (ne_of_gt hr) (by simpa using hval.symm)

  have h0_notmem : (0 : Fin r.succ) ∉ t := by
    intro h0
    rcases Finset.mem_map.1 (by simpa [t] using h0) with ⟨j, _hj, hj0⟩
    have hval : (j : ℕ) + 1 = 0 := by
      simpa [f] using congrArg Fin.val hj0
    have : Nat.succ (j : ℕ) = 0 := by
      simpa [Nat.succ_eq_add_one] using hval
    exact Nat.succ_ne_zero _ this

  have hlast_notmem : (Fin.last r) ∉ t := by
    intro hlast
    rcases Finset.mem_map.1 (by simpa [t] using hlast) with ⟨j, _hj, hjlast⟩
    have hval : (j : ℕ) + 1 = r := by
      simpa [f] using congrArg Fin.val hjlast
    have hjle : (j : ℕ) + 1 ≤ r - 1 := Nat.succ_le_of_lt j.2
    have hr1 : r - 1 < r := tsub_lt_self hr (by decide : 0 < (1 : ℕ))
    have hjlt : (j : ℕ) + 1 < r := lt_of_le_of_lt hjle hr1
    exact (ne_of_lt hjlt) hval

  have h0_notmem' : (0 : Fin r.succ) ∉ insert (Fin.last r) t := by
    simp [Finset.mem_insert, h0_notmem, h0last]

  have hcard_boundaries_symm : ((compositionAsSetEquiv r).symm s).boundaries.card = s.card + 2 := by
    have hcard_last : (insert (Fin.last r) t).card = t.card + 1 :=
      Finset.card_insert_of_notMem hlast_notmem
    have hcard_zero : (insert (0 : Fin r.succ) (insert (Fin.last r) t)).card =
        (insert (Fin.last r) t).card + 1 :=
      Finset.card_insert_of_notMem h0_notmem'
    calc
      ((compositionAsSetEquiv r).symm s).boundaries.card =
          (insert (0 : Fin r.succ) (insert (Fin.last r) t)).card := by
            simpa [hbound]
      _ = (insert (Fin.last r) t).card + 1 := by
            simpa using hcard_zero
      _ = (t.card + 1) + 1 := by
            simp [hcard_last, Nat.add_assoc]
      _ = t.card + 2 := by
            omega
      _ = s.card + 2 := by
            simp [htcard]

  -- Relate back to `c` using the left inverse of the equivalence.
  have hc : (compositionAsSetEquiv r).symm s = c := by
    simpa [s] using ((compositionAsSetEquiv r).left_inv c)

  have hcard_boundaries : c.boundaries.card = s.card + 2 := by
    simpa [hc] using hcard_boundaries_symm

  have hlen : c.length = s.card + 1 := by
    have hlen_succ : c.length + 1 = s.card + 2 := by
      calc
        c.length + 1 = c.boundaries.card := by
          simpa using (c.card_boundaries_eq_succ_length).symm
        _ = s.card + 2 := hcard_boundaries
    -- cancel the trailing `+ 1`
    have : Nat.succ c.length = Nat.succ (s.card + 1) := by
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlen_succ
    exact Nat.succ_injective this

  have hs : s.card = c.length - 1 := by
    calc
      s.card = (s.card + 1) - 1 := by simp
      _ = c.length - 1 := by simpa [hlen]

  simpa [s] using hs

theorem composition_length_card_choose (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
  Fintype.card {c : Composition r // c.length = k} = Nat.choose (r - 1) (k - 1) := by
  classical
  have hcard :
      Fintype.card {c : Composition r // c.length = k} =
        Fintype.card {s : Finset (Fin (r - 1)) // s.card = k - 1} := by
    refine Fintype.card_congr ?_
    have e₁ :
        {c : Composition r // c.length = k} ≃ {c : CompositionAsSet r // c.length = k} := by
      refine (compositionEquiv r).subtypeEquiv
        (p := fun c : Composition r => c.length = k)
        (q := fun c : CompositionAsSet r => c.length = k) ?_
      intro c
      simp [compositionEquiv]
    have e₂ :
        {c : CompositionAsSet r // c.length = k} ≃
          {s : Finset (Fin (r - 1)) // s.card = k - 1} := by
      refine (compositionAsSetEquiv r).subtypeEquiv
        (p := fun c : CompositionAsSet r => c.length = k)
        (q := fun s : Finset (Fin (r - 1)) => s.card = k - 1) ?_
      intro c
      have hcardEq : (compositionAsSetEquiv r c).card = c.length - 1 := by
        simpa using (compositionAsSetEquiv_card_eq_length_pred r c hr)
      constructor
      · intro hlen
        simpa [hcardEq, hlen]
      · intro hcardk
        have hsub : c.length - 1 = k - 1 := by
          simpa [hcardEq] using hcardk
        have hposLen : 0 < c.length := by
          have : 0 < c.toComposition.length :=
            (Composition.length_pos_iff (c := c.toComposition)).2 hr
          simpa using this
        have h1 : (c.length - 1) + 1 = (k - 1) + 1 :=
          congrArg (fun n => n + 1) hsub
        have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
        have hl1 : 1 ≤ c.length := Nat.succ_le_of_lt hposLen
        simpa [Nat.sub_add_cancel hl1, Nat.sub_add_cancel hk1] using h1
    exact e₁.trans e₂
  rw [hcard]
  simpa using (Fintype.card_finset_len (α := Fin (r - 1)) (k := k - 1))

theorem composition_prod_rpow_le (r : ℕ) (c : Composition r) (p : ℝ) (hp : 0 ≤ p) :
  (∏ i : Fin c.length, Real.rpow (c.blocksFun i) p)
    ≤ Real.rpow ((r : ℝ) / (c.length : ℝ)) (p * c.length) := by
  classical
  cases r with
  | zero =>
      have hlen : c.length = 0 := (Composition.length_eq_zero (c := c)).2 rfl
      haveI : IsEmpty (Fin c.length) := by
        simpa [hlen] using (by infer_instance : IsEmpty (Fin 0))
      simp [hlen]
  | succ r =>
      have hlen_ne_nat : c.length ≠ 0 := by
        intro h
        have : (Nat.succ r : ℕ) = 0 := (Composition.length_eq_zero (c := c)).1 h
        exact Nat.succ_ne_zero r this
      have hlen_ne : (c.length : ℝ) ≠ 0 := by
        exact_mod_cast hlen_ne_nat

      let s : Finset (Fin c.length) := Finset.univ
      let w : Fin c.length → ℝ := fun _ => 1 / (c.length : ℝ)
      let z : Fin c.length → ℝ := fun i => (c.blocksFun i : ℝ)

      have hw : ∀ i ∈ s, 0 ≤ w i := by
        intro i hi
        simp [w]

      have hw' : (∑ i ∈ s, w i) = 1 := by
        simp [s, w, hlen_ne]

      have hz : ∀ i ∈ s, 0 ≤ z i := by
        intro i hi
        simp [z]

      have hAMGM : (∏ i ∈ s, z i ^ w i) ≤ ∑ i ∈ s, w i * z i := by
        exact Real.geom_mean_le_arith_mean_weighted (s := s) w z hw hw' hz

      have hsum_wz : (∑ i ∈ s, w i * z i) = (1 / (c.length : ℝ)) * (∑ i ∈ s, z i) := by
        simpa [w] using (Finset.mul_sum s (fun i => z i) (1 / (c.length : ℝ))).symm

      have hsum_z : (∑ i ∈ s, z i) = (Nat.succ r : ℝ) := by
        simpa [s, z] using
          (show (∑ i : Fin c.length, (c.blocksFun i : ℝ)) = (Nat.succ r : ℝ) from by
            exact_mod_cast c.sum_blocksFun)

      have hAMGM' : (∏ i ∈ s, z i ^ w i) ≤ (Nat.succ r : ℝ) / (c.length : ℝ) := by
        have : (∑ i ∈ s, w i * z i) = (Nat.succ r : ℝ) / (c.length : ℝ) := by
          calc
            (∑ i ∈ s, w i * z i) = (1 / (c.length : ℝ)) * (∑ i ∈ s, z i) := hsum_wz
            _ = (1 / (c.length : ℝ)) * (Nat.succ r : ℝ) := by simp [hsum_z]
            _ = (Nat.succ r : ℝ) / (c.length : ℝ) := by ring
        simpa [this] using hAMGM

      have hpow : (∏ i ∈ s, z i ^ w i) ^ (p * c.length) ≤ ((Nat.succ r : ℝ) / (c.length : ℝ)) ^ (p * c.length) := by
        have hA0 : 0 ≤ ∏ i ∈ s, z i ^ w i := by
          refine Finset.prod_nonneg ?_
          intro i hi
          have hz0 : 0 ≤ z i := hz i hi
          exact Real.rpow_nonneg hz0 (w i)
        have hexp : 0 ≤ p * (c.length : ℝ) := by
          exact mul_nonneg hp (by exact_mod_cast (Nat.zero_le c.length))
        exact Real.rpow_le_rpow hA0 hAMGM' hexp

      -- rewrite the left side of hpow to the desired product
      have hprod_eq : (∏ i ∈ s, z i ^ w i) ^ (p * c.length) = ∏ i ∈ s, z i ^ p := by
        -- first, turn the product into a single rpow
        have hz_nonneg : ∀ i ∈ s, 0 ≤ z i := hz
        have hprod1 : (∏ i ∈ s, z i ^ w i) = (∏ i ∈ s, z i) ^ (1 / (c.length : ℝ)) := by
          -- use finset_prod_rpow
          simpa [w] using (Real.finset_prod_rpow s z hz_nonneg (1 / (c.length : ℝ)))
        -- now raise to p * c.length
        --
        --
        have hZ0 : 0 ≤ ∏ i ∈ s, z i := by
          refine Finset.prod_nonneg ?_
          intro i hi
          exact hz i hi
        -- use rpow_mul to combine exponents
        calc
          (∏ i ∈ s, z i ^ w i) ^ (p * (c.length : ℝ))
              = ((∏ i ∈ s, z i) ^ (1 / (c.length : ℝ))) ^ (p * (c.length : ℝ)) := by simp [hprod1]
          _ = (∏ i ∈ s, z i) ^ ((1 / (c.length : ℝ)) * (p * (c.length : ℝ))) := by
              simpa [mul_assoc] using (Real.rpow_mul hZ0 (1 / (c.length : ℝ)) (p * (c.length : ℝ))).symm
          _ = (∏ i ∈ s, z i) ^ p := by
              -- simplify the exponent
              field_simp [hlen_ne]
          _ = ∏ i ∈ s, z i ^ p := by
              -- distribute rpow over product
              symm
              simpa using (Real.finset_prod_rpow s z hz_nonneg p)

      -- combine
      have hfinal_finset : (∏ i ∈ s, z i ^ p) ≤ ((Nat.succ r : ℝ) / (c.length : ℝ)) ^ (p * c.length) := by
        -- rewrite using hprod_eq
        --
        --
        have := hpow
        --
        --
        simpa [hprod_eq] using this

      -- finish by rewriting back to the statement
      simpa [s, z] using hfinal_finset


def isGoodDLemma5 (n : ℕ) (c p : ℝ) (d : ℕ) : Prop :=
  (d ≥ 3) ∧ (Real.rpow n d > 4 * (Real.exp 1) * (n + c) * (Real.rpow d (p + 1)))

theorem k_mul_log_s_div_k_le_s_sub_k (s k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) :
  (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ)) ≤ (s : ℝ) - (k : ℝ) := by
  have hkposNat : 0 < k := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hk
  have hsposNat : 0 < s := Nat.lt_of_lt_of_le hkposNat hks
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hkposNat
  have hspos : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast hsposNat
  have htpos : (0 : ℝ) < (s : ℝ) / (k : ℝ) := by
    exact div_pos hspos hkpos
  have hlog :
      Real.log ((s : ℝ) / (k : ℝ)) ≤ (s : ℝ) / (k : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos htpos
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := le_of_lt hkpos
  have hmul :
      (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ)) ≤ (k : ℝ) * ((s : ℝ) / (k : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left hlog hk0
  have hkne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hkposNat)
  calc
    (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ))
        ≤ (k : ℝ) * ((s : ℝ) / (k : ℝ) - 1) := hmul
    _ = (s : ℝ) - (k : ℝ) := by
      field_simp [hkne]

theorem length_prod_eq_sum_length (n : ℕ) (l : List (FreeMonoid (Fin n))) : (l.prod).length = (l.map FreeMonoid.length).sum := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      simp [ih, FreeMonoid.length_mul]


theorem composition_of_list_lengths (n : ℕ) (l : List (FreeMonoid (Fin n))) (r : ℕ)
  (hpos : ∀ x, x ∈ l → 1 ≤ x.length)
  (hprod : (l.prod).length = r) :
  ∃ c : Composition r, c.blocks = l.map FreeMonoid.length := by
  refine ⟨⟨l.map FreeMonoid.length, ?_, ?_⟩, rfl⟩
  · intro i hi
    rcases List.mem_map.1 hi with ⟨x, hx, rfl⟩
    -- `hpos` gives `1 ≤ x.length`, hence `0 < x.length`.
    exact (Nat.succ_le_iff.mp (hpos x hx))
  ·
    have hlen : (l.prod).length = (l.map FreeMonoid.length).sum :=
      length_prod_eq_sum_length n l
    -- Rewrite the sum using `hlen` and `hprod`.
    exact hlen.symm.trans hprod

theorem finite_rep_lists (n : ℕ) (X : Set (FreeMonoid (Fin n))) (s r : ℕ) :
  ({l : List (FreeMonoid (Fin n)) |
      l.length ≤ s ∧ (∀ x, x ∈ l → x ∈ X) ∧ (l.prod).length = r}).Finite := by
  classical
  -- Words of length at most `r`
  let S : Set (FreeMonoid (Fin n)) := {w | w.length ≤ r}
  have hS : S.Finite := by
    simpa [S, FreeMonoid, FreeMonoid.length] using
      (List.finite_length_le (α := Fin n) r)

  -- Lists of elements of `S` of length at most `s` form a finite set after coercion.
  have hU : ({l : List (FreeMonoid (Fin n)) | l.length ≤ s ∧ ∀ x, x ∈ l → x ∈ S}).Finite := by
    classical
    letI : Fintype S := hS.fintype
    have hListS : ({l : List S | l.length ≤ s}).Finite := List.finite_length_le (α := S) s
    have hImage :
        ((fun l : List S => l.map (fun x : S => (x : FreeMonoid (Fin n)))) ''
            {l : List S | l.length ≤ s}).Finite :=
      hListS.image _
    refine hImage.subset ?_
    intro l hl
    rcases hl with ⟨hlen, hall⟩
    -- Lift the list to a list in the subtype `S` using `Set.range_list_map_coe`.
    have hlrange : l ∈ Set.range (List.map ((↑) : S → FreeMonoid (Fin n))) := by
      -- `hall` exactly says all entries of `l` lie in `S`.
      rw [Set.range_list_map_coe (s := S)]
      intro x hx
      exact hall x hx
    rcases hlrange with ⟨lS, rfl⟩
    refine ⟨lS, ?_, rfl⟩
    -- `List.map` does not change length.
    simpa using hlen

  -- Our target set is a subset of the above finite set, using the length bound on `l.prod`.
  refine hU.subset ?_
  intro l hl
  rcases hl with ⟨hlen, _hX, hprod⟩
  refine ⟨hlen, ?_⟩
  intro x hx
  -- Use the axiom about the length of a product.
  have hsum : (l.map FreeMonoid.length).sum = r :=
    (length_prod_eq_sum_length n l).symm.trans hprod

  have hxmem : x.length ∈ l.map FreeMonoid.length := by
    -- `x.length` occurs in the list of lengths since `x` occurs in `l`.
    refine (List.mem_map.2 ?_)
    exact ⟨x, hx, rfl⟩

  have hxle_sum : x.length ≤ (l.map FreeMonoid.length).sum := by
    have hnonneg : ∀ m ∈ l.map FreeMonoid.length, (0 : ℕ) ≤ m := by
      intro m hm
      exact Nat.zero_le m
    exact List.single_le_sum (l := l.map FreeMonoid.length) hnonneg _ hxmem

  have hxle : x.length ≤ r := by
    simpa [hsum] using hxle_sum
  simpa [S] using hxle


theorem mem_A_iff_length_eq_one (n : ℕ) (w : FreeMonoid (Fin n)) : w ∈ A n ↔ w.length = 1 := by
  constructor
  · intro hw
    rcases hw with ⟨i, rfl⟩
    exact FreeMonoid.length_of i
  · intro hlen
    have hlen' : FreeMonoid.length w = 1 := by
      simpa using hlen
    rcases (FreeMonoid.length_eq_one.mp hlen') with ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    rfl

theorem mem_Ball_A_of_length_le (n r : ℕ) (w : FreeMonoid (Fin n)) : w.length ≤ r → w ∈ Ball r (A n) := by
  intro hw
  refine ⟨(FreeMonoid.toList w).map (fun i : Fin n => ([i] : FreeMonoid (Fin n))), ?_⟩
  refine ⟨?_, ?_⟩
  · simpa using hw
  · refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_map.1 hx with ⟨i, hi, rfl⟩
      exact ⟨i, rfl⟩
    ·
      apply FreeMonoid.toList.injective
      -- reduce to a statement about lists
      simp [FreeMonoid.toList_prod]
      -- now prove that flattening singletons gives back the list
      induction FreeMonoid.toList w with
      | nil =>
          simp
      | cons a t ih =>
          simp [ih]


theorem nat_le_two_pow (s : ℕ) : s ≤ 2 ^ s := by
  calc
    s = 1 * s := by simp
    _ ≤ 2 * s := by
      exact Nat.mul_le_mul_right s (by decide : (1 : ℕ) ≤ 2)
    _ ≤ 2 ^ s := by
      simpa [Nat.mul_comm] using
        (Nat.mul_le_pow (a := 2) (b := s) (by decide : (2 : ℕ) ≠ 1))


theorem ncard_A (n : ℕ) : Set.ncard (A n) = n := by
  classical
  simpa [A, Nat.card_fin] using
    (Set.ncard_range_of_injective
      (f := fun i : Fin n => ([i] : FreeMonoid (Fin n)))
      (by
        intro i j h
        simpa using (List.singleton_injective h)))

theorem ncard_generators_length_le (n : ℕ) (G : Set (FreeMonoid (Fin n))) (c p : ℝ)
  (hc : 0 < c) (hp : 0 ≤ p)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ l : ℕ, 1 ≤ l → (Set.ncard { x ∈ (G ∪ (A n)) | x.length = l } ≤ (n + c) * Real.rpow l p) := by
  classical
  intro l hl
  cases l with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hl)
  | succ l =>
      cases l with
      | zero =>
          -- l = 1
          have hset : { x ∈ (G ∪ A n) | x.length = (Nat.succ 0) } = A n := by
            ext x
            constructor
            · intro hx
              rcases hx with ⟨hxU, hxlen⟩
              rcases (FreeMonoid.length_eq_one.mp hxlen) with ⟨i, rfl⟩
              exact ⟨i, rfl⟩
            · intro hxA
              refine ⟨?_, ?_⟩
              · exact Or.inr hxA
              · rcases hxA with ⟨i, rfl⟩
                exact FreeMonoid.length_of i
          -- rewrite goal
          rw [hset]
          -- compute ncard A
          have hcardA : (A n).ncard = n := by
            simpa [A] using
              (Set.ncard_range_of_injective (f := fun i : Fin n => ([i] : FreeMonoid (Fin n)))
                (by
                  intro i j hij
                  exact FreeMonoid.of_injective hij))
          have hcardA_real : (Set.ncard (A n) : ℝ) = (n : ℝ) := by
            exact_mod_cast hcardA
          have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
          have hnle : (n : ℝ) ≤ (n : ℝ) + c := le_add_of_nonneg_right hc0
          have hle : (Set.ncard (A n) : ℝ) ≤ (n : ℝ) + c := by
            simpa [hcardA_real] using hnle
          -- finish by simp on rpow
          simpa using hle
      | succ l =>
          -- l ≥ 2
          -- let L = l+2
          have hLge2 : (2 : ℕ) ≤ Nat.succ (Nat.succ l) := by
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le l))
          have hset : { x ∈ (G ∪ A n) | x.length = Nat.succ (Nat.succ l) } =
              { x ∈ G | x.length = Nat.succ (Nat.succ l) } := by
            ext x
            constructor
            · intro hx
              rcases hx with ⟨hxU, hxlen⟩
              have hxG : x ∈ G := by
                cases hxU with
                | inl hxG =>
                    exact hxG
                | inr hxA =>
                    -- contradiction: element of A has length 1
                    rcases hxA with ⟨i, rfl⟩
                    have hlen1 : ([i] : FreeMonoid (Fin n)).length = 1 := FreeMonoid.length_of i
                    have h1eq : (1 : ℕ) = Nat.succ (Nat.succ l) := by
                      -- 1 = length [i] = ...
                      exact hlen1.symm.trans hxlen
                    have h1lt : (1 : ℕ) < Nat.succ (Nat.succ l) :=
                      Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hLge2
                    exact (False.elim ((Nat.ne_of_lt h1lt) h1eq))
              exact ⟨hxG, hxlen⟩
            · intro hx
              rcases hx with ⟨hxG, hxlen⟩
              exact ⟨Or.inl hxG, hxlen⟩
          -- rewrite with hset
          rw [hset]
          -- apply bound on G
          have hbound : (Set.ncard { x ∈ G | x.length = Nat.succ (Nat.succ l) } : ℝ) ≤
              c * Real.rpow (Nat.succ (Nat.succ l)) p := by
            exact hG (Nat.succ (Nat.succ l)) hLge2
          -- enlarge constant from c to n+c
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (Nat.zero_le n)
          have hc_le : c ≤ (n : ℝ) + c := le_add_of_nonneg_left hn0
          have hrpow_nonneg : 0 ≤ Real.rpow (Nat.succ (Nat.succ l)) p := by
            -- base is nonnegative
            apply Real.rpow_nonneg
            exact_mod_cast (Nat.zero_le (Nat.succ (Nat.succ l)))
          have hmul : c * Real.rpow (Nat.succ (Nat.succ l)) p ≤
              ((n : ℝ) + c) * Real.rpow (Nat.succ (Nat.succ l)) p := by
            exact mul_le_mul_of_nonneg_right hc_le hrpow_nonneg
          -- combine
          exact le_trans hbound hmul

theorem ncard_setOf_forall_mem_le_prod (ι α : Type*) [Fintype ι] (T : ι → Set α) :
  Set.ncard {f : ι → α | ∀ i, f i ∈ T i} ≤ ∏ i : ι, Set.ncard (T i) := by
  classical
  let S : Set (ι → α) := {f : ι → α | ∀ i, f i ∈ T i}
  have hNat : Nat.card S = ∏ i : ι, Nat.card (T i) := by
    let e : S ≃ (∀ i : ι, T i) :=
      { toFun := fun f i =>
          ⟨f.1 i,
            by
              have hf : f.1 ∈ S := f.2
              dsimp [S] at hf
              exact hf i⟩
        invFun := fun g =>
          ⟨fun i => (g i).1,
            by
              dsimp [S]
              intro i
              exact (g i).2⟩
        left_inv := by
          intro f
          ext i
          rfl
        right_inv := by
          intro g
          funext i
          ext
          rfl }
    calc
      Nat.card S = Nat.card (∀ i : ι, T i) := Nat.card_congr e
      _ = ∏ i : ι, Nat.card (T i) := by
        simpa using (Nat.card_pi (β := fun i : ι => T i))
  have hSet : Set.ncard S = ∏ i : ι, Set.ncard (T i) := by
    calc
      Set.ncard S = Nat.card S := (Set.Nat.card_coe_set_eq (s := S)).symm
      _ = ∏ i : ι, Nat.card (T i) := hNat
      _ = ∏ i : ι, Set.ncard (T i) := by
        simp [Set.Nat.card_coe_set_eq]
  simpa [S] using hSet.le

theorem ncard_lists_fixed_blocks_le_prod (n : ℕ) (X : Set (FreeMonoid (Fin n))) {r : ℕ} (c : Composition r) :
  Set.ncard
      {l : List (FreeMonoid (Fin n)) |
          l.length = c.length ∧ (∀ x, x ∈ l → x ∈ X) ∧ (l.map FreeMonoid.length = c.blocks)}
    ≤ ∏ i : Fin c.length, Set.ncard {x ∈ X | x.length = c.blocksFun i} := by
  classical
  let S : Set (List (FreeMonoid (Fin n))) :=
    {l : List (FreeMonoid (Fin n)) |
        l.length = c.length ∧ (∀ x, x ∈ l → x ∈ X) ∧ (l.map FreeMonoid.length = c.blocks)}
  let T : Fin c.length → Set (FreeMonoid (Fin n)) := fun i => {x ∈ X | x.length = c.blocksFun i}
  let F : Set (Fin c.length → FreeMonoid (Fin n)) := {f | ∀ i, f i ∈ T i}
  let encode : List (FreeMonoid (Fin n)) → (Fin c.length → FreeMonoid (Fin n)) :=
    fun l i => l.getD (i : ℕ) 1

  have h_maps : Set.MapsTo encode S F := by
    intro l hl
    rcases hl with ⟨hlen, hX, hblocks⟩
    intro i
    have hi : (i : ℕ) < l.length := by
      simpa [hlen] using i.isLt
    have hX' : ∀ (j : ℕ) (hj : j < l.length), l[j] ∈ X := by
      have : ∀ x ∈ l, x ∈ X := by
        intro x hx
        exact hX x hx
      exact (List.forall_mem_iff_getElem (l := l) (p := fun x => x ∈ X)).1 this
    refine ⟨?_, ?_⟩
    · have hget : encode l i = l[(i : ℕ)] := by
        dsimp [encode]
        exact (List.getD_eq_getElem (l := l) (d := (1 : FreeMonoid (Fin n))) hi)
      simpa [hget] using hX' (i : ℕ) hi
    · have hgetD : (l.map FreeMonoid.length).getD (i : ℕ) 0 = c.blocks.getD (i : ℕ) 0 := by
        simpa using congrArg (fun L : List ℕ => L.getD (i : ℕ) 0) hblocks
      have hL : (l.map FreeMonoid.length).getD (i : ℕ) 0 = (encode l i).length := by
        simpa [encode] using
          (List.getD_map (l := l) (d := (1 : FreeMonoid (Fin n))) (n := (i : ℕ))
            (f := FreeMonoid.length))
      have hR : c.blocks.getD (i : ℕ) 0 = c.blocksFun i := by
        have hci : (i : ℕ) < c.blocks.length := by
          simpa [Composition.blocks_length] using i.isLt
        have : c.blocks.getD (i : ℕ) 0 = c.blocks[(i : ℕ)] :=
          List.getD_eq_getElem (l := c.blocks) (d := (0 : ℕ)) hci
        simpa [Composition.blocksFun, this]
      have : (encode l i).length = c.blocks.getD (i : ℕ) 0 :=
        hL.symm.trans hgetD
      exact this.trans hR

  have h_inj : Set.InjOn encode S := by
    intro l₁ hl₁ l₂ hl₂ henc
    rcases hl₁ with ⟨h₁len, -, -⟩
    rcases hl₂ with ⟨h₂len, -, -⟩
    apply (List.ext_get_iff).2
    refine ⟨by simpa [h₁len, h₂len], ?_⟩
    intro m hm₁ hm₂
    have hm : m < c.length := by
      simpa [h₁len] using hm₁
    let i : Fin c.length := ⟨m, hm⟩
    have hi₁ : (i : ℕ) < l₁.length := by
      simpa [h₁len] using i.isLt
    have hi₂ : (i : ℕ) < l₂.length := by
      simpa [h₂len] using i.isLt
    have := congrArg (fun f => f i) henc
    have hget₁ : encode l₁ i = l₁[(i : ℕ)] := by
      dsimp [encode]
      exact List.getD_eq_getElem (l := l₁) (d := (1 : FreeMonoid (Fin n))) hi₁
    have hget₂ : encode l₂ i = l₂[(i : ℕ)] := by
      dsimp [encode]
      exact List.getD_eq_getElem (l := l₂) (d := (1 : FreeMonoid (Fin n))) hi₂
    simpa [hget₁, hget₂] using this

  have hTfinite : ∀ i : Fin c.length, (T i).Finite := by
    intro i
    have hlen : ({x : FreeMonoid (Fin n) | x.length = c.blocksFun i}).Finite := by
      simpa using (List.finite_length_eq (α := Fin n) (n := c.blocksFun i))
    refine hlen.subset ?_
    intro x hx
    exact hx.2

  have hFfinite : F.Finite := by
    simpa [F] using
      (Set.Finite.pi' (ι := Fin c.length) (κ := fun _ : Fin c.length => FreeMonoid (Fin n))
        (t := T) hTfinite)

  have hS_le_F : Set.ncard S ≤ Set.ncard F := by
    refine Set.ncard_le_ncard_of_injOn (s := S) (t := F) encode ?_ h_inj (ht := hFfinite)
    intro l hl
    exact h_maps hl

  have hF_le_prod : Set.ncard F ≤ ∏ i : Fin c.length, Set.ncard (T i) := by
    simpa [F] using
      (ncard_setOf_forall_mem_le_prod (ι := Fin c.length) (α := FreeMonoid (Fin n)) T)

  simpa [S, T] using hS_le_F.trans hF_le_prod

theorem ncard_words_length_eq (n r : ℕ) : Set.ncard {w : FreeMonoid (Fin n) | w.length = r} = n ^ r := by
  classical
  -- Compare the set of words of length `r` with the type of vectors of length `r`.
  have hcongr :
      Set.ncard {w : FreeMonoid (Fin n) | w.length = r} =
        Set.ncard (Set.univ : Set (List.Vector (Fin n) r)) := by
    refine
      Set.ncard_congr (s := {w : FreeMonoid (Fin n) | w.length = r})
        (t := (Set.univ : Set (List.Vector (Fin n) r)))
        (f := fun w hw => (⟨w, hw⟩ : List.Vector (Fin n) r)) ?_ ?_ ?_
    · intro w hw
      simp
    · intro a b ha hb hEq
      -- Injectivity follows by comparing underlying lists.
      exact congrArg (fun v : List.Vector (Fin n) r => v.1) hEq
    · intro v hv
      refine ⟨v.1, v.2, ?_⟩
      -- Surjectivity is by construction.
      ext
      rfl
  -- Now compute the cardinality using the known formula for vectors.
  calc
    Set.ncard {w : FreeMonoid (Fin n) | w.length = r}
        = Set.ncard (Set.univ : Set (List.Vector (Fin n) r)) := hcongr
    _ = Nat.card (List.Vector (Fin n) r) := by
        simpa using (Set.ncard_univ (List.Vector (Fin n) r))
    _ = Fintype.card (List.Vector (Fin n) r) := by
        simpa using (Nat.card_eq_fintype_card (α := List.Vector (Fin n) r))
    _ = Fintype.card (Fin n) ^ r := by
        simpa using (card_vector (α := Fin n) r)
    _ = n ^ r := by
        simp

theorem one_le_log_nat_of_three_le (d : ℕ) (hd : 3 ≤ d) : (1 : ℝ) ≤ Real.log (d : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have hd0' : (0 : ℕ) < d := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hd
    exact_mod_cast hd0'
  have hExp1_le_3 : Real.exp (1 : ℝ) ≤ (3 : ℝ) := by
    have hD : (2.7182818286 : ℝ) < (3 : ℝ) := by
      norm_num
    have hExp_lt_3 : Real.exp (1 : ℝ) < (3 : ℝ) := lt_trans Real.exp_one_lt_d9 hD
    exact le_of_lt hExp_lt_3
  have h3_le_d : (3 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hExp_le_d : Real.exp (1 : ℝ) ≤ (d : ℝ) := le_trans hExp1_le_3 h3_le_d
  exact (Real.le_log_iff_exp_le hd0).2 hExp_le_d


theorem rep_lists_slice_eq_iUnion_composition (n : ℕ) (X : Set (FreeMonoid (Fin n))) (r k : ℕ) :
  {l : List (FreeMonoid (Fin n)) |
      l.length = k ∧ (∀ x, x ∈ l → x ∈ X) ∧
        (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = r}
    = ⋃ c : {c : Composition r // c.length = k},
        {l : List (FreeMonoid (Fin n)) |
            l.length = k ∧ (∀ x, x ∈ l → x ∈ X) ∧ (l.map FreeMonoid.length = c.1.blocks)} := by
  ext l
  constructor
  · intro hl
    rcases hl with ⟨hlen, hX, hpos, hprod⟩
    rcases composition_of_list_lengths n l r hpos hprod with ⟨c, hc⟩
    have hclen : c.length = k := by
      calc
        c.length = c.blocks.length := by simpa using (c.blocks_length).symm
        _ = (l.map FreeMonoid.length).length := by simpa [hc]
        _ = l.length := by simp
        _ = k := hlen
    refine (Set.mem_iUnion).2 ?_
    refine ⟨⟨c, hclen⟩, ?_⟩
    exact ⟨hlen, hX, hc.symm⟩
  · intro hl
    rcases (Set.mem_iUnion).1 hl with ⟨c, hlc⟩
    rcases hlc with ⟨hlen, hX, hmap⟩
    have hpos : ∀ x, x ∈ l → 1 ≤ x.length := by
      intro x hx
      have hxlen : x.length ∈ c.1.blocks := by
        have : x.length ∈ l.map FreeMonoid.length := by
          refine List.mem_map.2 ?_
          exact ⟨x, hx, rfl⟩
        simpa [hmap] using this
      exact c.1.one_le_blocks hxlen
    have hprod : (l.prod).length = r := by
      calc
        (l.prod).length = (l.map FreeMonoid.length).sum := length_prod_eq_sum_length n l
        _ = c.1.blocks.sum := by simpa [hmap]
        _ = r := by simpa using c.1.blocks_sum
    exact ⟨hlen, hX, hpos, hprod⟩

theorem s_sub_k_le_mul_log_d (d s k : ℕ) (hks : k ≤ s) (hd : 3 ≤ d) :
  (s : ℝ) - (k : ℝ) ≤ ((s : ℝ) - (k : ℝ)) * Real.log (d : ℝ) := by
  set a : ℝ := (s : ℝ) - (k : ℝ) with ha
  have ha_nonneg : 0 ≤ a := by
    have hks' : (k : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hks
    have : 0 ≤ (s : ℝ) - (k : ℝ) := by
      exact sub_nonneg.mpr hks'
    simpa [ha] using this
  have hlog : (1 : ℝ) ≤ Real.log (d : ℝ) :=
    one_le_log_nat_of_three_le d hd
  have : a ≤ a * Real.log (d : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlog ha_nonneg
    simpa using this
  simpa [ha] using this

theorem rpow_ds_div_k_le_rpow_d_pow_s (d s k : ℕ) (p : ℝ)
  (hp : 0 ≤ p) (hs : 1 ≤ s) (hk : 1 ≤ k) (hks : k ≤ s) (hd : 3 ≤ d) :
  (((d * s : ℕ) : ℝ) / (k : ℝ)) ^ (p * k)
    ≤ (d : ℝ) ^ (p * s) := by
  classical

  -- work with the real base `b = d*s/k`
  let b : ℝ := (d : ℝ) * (s : ℝ) / (k : ℝ)

  -- rewrite `b` as `d * (s/k)`
  have hb : b = (d : ℝ) * ((s : ℝ) / (k : ℝ)) := by
    unfold b
    simpa [mul_assoc] using (mul_div_assoc (d : ℝ) (s : ℝ) (k : ℝ))

  -- positivity facts
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 3) hd)
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hk)
  have hspos : (0 : ℝ) < (s : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hs)
  have hskpos : (0 : ℝ) < (s : ℝ) / (k : ℝ) := by
    exact div_pos hspos hkpos

  have hbpos : (0 : ℝ) < b := by
    -- b = d * (s/k)
    have : (0 : ℝ) < (d : ℝ) * ((s : ℝ) / (k : ℝ)) := mul_pos hdpos hskpos
    simpa [hb] using this

  -- main log inequality: k * log b ≤ s * log d
  have hlog : (k : ℝ) * Real.log b ≤ (s : ℝ) * Real.log (d : ℝ) := by
    -- start from k*log(s/k) ≤ (s-k)*log d
    have h1 : (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ)) ≤ (s : ℝ) - (k : ℝ) :=
      k_mul_log_s_div_k_le_s_sub_k s k hk hks
    have h2 : (s : ℝ) - (k : ℝ) ≤ ((s : ℝ) - (k : ℝ)) * Real.log (d : ℝ) :=
      s_sub_k_le_mul_log_d d s k hks hd
    have hkslog : (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ)) ≤ ((s : ℝ) - (k : ℝ)) * Real.log (d : ℝ) :=
      le_trans h1 h2

    -- add `k*log d` to both sides
    have hadd : (k : ℝ) * Real.log (d : ℝ) + (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ))
        ≤ (k : ℝ) * Real.log (d : ℝ) + ((s : ℝ) - (k : ℝ)) * Real.log (d : ℝ) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hkslog ((k : ℝ) * Real.log (d : ℝ)))

    have hrhs : (k : ℝ) * Real.log (d : ℝ) + ((s : ℝ) - (k : ℝ)) * Real.log (d : ℝ)
        = (s : ℝ) * Real.log (d : ℝ) := by
      ring

    -- `log (d*(s/k)) = log d + log(s/k)`
    have hlogmul : Real.log ((d : ℝ) * ((s : ℝ) / (k : ℝ)))
        = Real.log (d : ℝ) + Real.log ((s : ℝ) / (k : ℝ)) := by
      have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
      have hskne : (s : ℝ) / (k : ℝ) ≠ 0 := ne_of_gt hskpos
      simpa using (Real.log_mul hdne hskne)

    have hlhs : (k : ℝ) * Real.log b
        = (k : ℝ) * Real.log (d : ℝ) + (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ)) := by
      -- rewrite `b` and distribute
      calc
        (k : ℝ) * Real.log b
            = (k : ℝ) * Real.log ((d : ℝ) * ((s : ℝ) / (k : ℝ))) := by
                simp [hb]
        _ = (k : ℝ) * (Real.log (d : ℝ) + Real.log ((s : ℝ) / (k : ℝ))) := by
                simp [hlogmul]
        _ = (k : ℝ) * Real.log (d : ℝ) + (k : ℝ) * Real.log ((s : ℝ) / (k : ℝ)) := by
                ring

    -- conclude
    simpa [hlhs, hrhs] using hadd

  -- multiply the log inequality by `p` and exponentiate
  have hexp : (p * k) * Real.log b ≤ (p * s) * Real.log (d : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlog hp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

  have hexp' : Real.exp ((p * k) * Real.log b) ≤ Real.exp ((p * s) * Real.log (d : ℝ)) :=
    (Real.exp_le_exp).2 hexp

  -- rewrite back in terms of `rpow`
  have hbpos' : (0 : ℝ) < b := hbpos
  have hdpos' : (0 : ℝ) < (d : ℝ) := hdpos

  -- final `simp` uses `b` definition
  -- note: left base in goal is `((d*s):ℝ)/k = b`
  simpa [b, Nat.cast_mul, Real.rpow_def_of_pos hbpos', Real.rpow_def_of_pos hdpos',
    mul_assoc, mul_left_comm, mul_comm] using hexp'


theorem ncard_rep_lists_slice_le (n : ℕ) (hn : 2 ≤ n)
  (G : Set (FreeMonoid (Fin n)))
  (c p : ℝ) (hc : 0 < c) (hp : 0 ≤ p)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ (s d k : ℕ), 1 ≤ s → 3 ≤ d → 1 ≤ k → k ≤ s →
    (Set.ncard
        { l : List (FreeMonoid (Fin n)) |
            l.length = k ∧ (∀ x, x ∈ l → x ∈ (G ∪ (A n))) ∧
              (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s } : ℝ)
      ≤ (Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s := by
  intro s d k hs hd hk hks
  classical
  let r : ℕ := d * s
  let X : Set (FreeMonoid (Fin n)) := G ∪ (A n)
  let ι := {c : Composition r // c.length = k}
  let T : ι → Set (List (FreeMonoid (Fin n))) :=
    fun comp =>
      { l : List (FreeMonoid (Fin n)) |
          l.length = k ∧ (∀ x, x ∈ l → x ∈ X) ∧ (l.map FreeMonoid.length = comp.1.blocks) }
  let S : Set (List (FreeMonoid (Fin n))) :=
    { l : List (FreeMonoid (Fin n)) |
        l.length = k ∧ (∀ x, x ∈ l → x ∈ X) ∧
          (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = r }

  have hS : S = ⋃ comp : ι, T comp := by
    simpa [S, T] using (rep_lists_slice_eq_iUnion_composition n X r k)

  have hnat : Set.ncard S ≤ ∑ comp : ι, Set.ncard (T comp) := by
    simpa [hS.symm, T] using (Set.ncard_iUnion_le_of_fintype (s := T))

  have hreal0 : (Set.ncard S : ℝ) ≤ ((∑ comp : ι, Set.ncard (T comp)) : ℝ) := by
    exact_mod_cast hnat

  have hcastsum : ((∑ comp : ι, Set.ncard (T comp)) : ℝ) = ∑ comp : ι, (Set.ncard (T comp) : ℝ) := by
    classical
    simpa using
      (Nat.cast_sum (R := ℝ) (s := (Finset.univ : Finset ι)) (f := fun comp => Set.ncard (T comp)))

  have hreal : (Set.ncard S : ℝ) ≤ ∑ comp : ι, (Set.ncard (T comp) : ℝ) := by
    simpa [hcastsum] using hreal0

  -- bound each fiber
  have hfiber : ∀ comp : ι,
      (Set.ncard (T comp) : ℝ)
        ≤ (n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k) := by
    intro comp
    have hnat' : Set.ncard (T comp) ≤
        ∏ i : Fin comp.1.length,
          Set.ncard {x ∈ X | x.length = comp.1.blocksFun i} := by
      simpa [T, comp.2] using (ncard_lists_fixed_blocks_le_prod n X (c := comp.1))
    have hreal' : (Set.ncard (T comp) : ℝ) ≤
        ∏ i : Fin comp.1.length, (Set.ncard {x ∈ X | x.length = comp.1.blocksFun i} : ℝ) := by
      have hcast : (Set.ncard (T comp) : ℝ) ≤
          ((∏ i : Fin comp.1.length, Set.ncard {x ∈ X | x.length = comp.1.blocksFun i}) : ℝ) := by
        exact_mod_cast hnat'
      classical
      have hcastprod :
          ((∏ i : Fin comp.1.length, Set.ncard {x ∈ X | x.length = comp.1.blocksFun i}) : ℝ)
            = ∏ i : Fin comp.1.length, (Set.ncard {x ∈ X | x.length = comp.1.blocksFun i} : ℝ) := by
        simpa using
          (Nat.cast_prod (R := ℝ)
            (s := (Finset.univ : Finset (Fin comp.1.length)))
            (f := fun i : Fin comp.1.length =>
              Set.ncard {x ∈ X | x.length = comp.1.blocksFun i}))
      simpa [hcastprod] using hcast

    have hfac : ∀ i : Fin comp.1.length,
        (Set.ncard {x ∈ X | x.length = comp.1.blocksFun i} : ℝ)
          ≤ (n + c) * Real.rpow (comp.1.blocksFun i) p := by
      intro i
      have :=
        ncard_generators_length_le n G c p hc hp hG (comp.1.blocksFun i)
          (Composition.one_le_blocksFun (c := comp.1) i)
      simpa [X] using this

    have hprod_fac :
        (∏ i : Fin comp.1.length, (Set.ncard {x ∈ X | x.length = comp.1.blocksFun i} : ℝ))
          ≤ ∏ i : Fin comp.1.length, ((n + c) * Real.rpow (comp.1.blocksFun i) p) := by
      classical
      simpa using
        (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin comp.1.length)))
          (f := fun i : Fin comp.1.length =>
            (Set.ncard {x ∈ X | x.length = comp.1.blocksFun i} : ℝ))
          (g := fun i : Fin comp.1.length =>
            (n + c) * Real.rpow (comp.1.blocksFun i) p)
          (h0 := by
            intro i hi
            exact Nat.cast_nonneg (Set.ncard {x ∈ X | x.length = comp.1.blocksFun i}))
          (h1 := by
            intro i hi
            simpa using hfac i))

    have htmp : (Set.ncard (T comp) : ℝ)
        ≤ ∏ i : Fin comp.1.length, ((n + c) * Real.rpow (comp.1.blocksFun i) p) := by
      exact le_trans hreal' hprod_fac

    have hsplit :
        (∏ i : Fin comp.1.length, ((n + c) * Real.rpow (comp.1.blocksFun i) p))
          = (∏ _i : Fin comp.1.length, (n + c)) *
              (∏ i : Fin comp.1.length, Real.rpow (comp.1.blocksFun i) p) := by
      classical
      simpa using (Finset.prod_mul_distrib :
        (∏ i : Fin comp.1.length, (n + c) * Real.rpow (comp.1.blocksFun i) p)
          = (∏ i : Fin comp.1.length, (n + c)) *
              (∏ i : Fin comp.1.length, Real.rpow (comp.1.blocksFun i) p))

    have hconst : (∏ _i : Fin comp.1.length, (n + c)) = (n + c) ^ comp.1.length := by
      classical
      simpa using
        (Finset.prod_const (n + c)
          (s := (Finset.univ : Finset (Fin comp.1.length))))

    have hbound1 : (Set.ncard (T comp) : ℝ) ≤
        (n + c) ^ comp.1.length *
          (∏ i : Fin comp.1.length, Real.rpow (comp.1.blocksFun i) p) := by
      have : (Set.ncard (T comp) : ℝ) ≤
          (∏ _i : Fin comp.1.length, (n + c)) *
            (∏ i : Fin comp.1.length, Real.rpow (comp.1.blocksFun i) p) := by
        exact le_trans htmp (le_of_eq hsplit)
      simpa [hconst, mul_assoc] using this

    have hrpow : (∏ i : Fin comp.1.length, Real.rpow (comp.1.blocksFun i) p)
        ≤ Real.rpow ((r : ℝ) / (comp.1.length : ℝ)) (p * comp.1.length) :=
      composition_prod_rpow_le r comp.1 p hp

    have hrpow' : (∏ i : Fin comp.1.length, Real.rpow (comp.1.blocksFun i) p)
        ≤ Real.rpow ((r : ℝ) / (k : ℝ)) (p * k) := by
      simpa [comp.2] using hrpow

    have hncp : 0 ≤ (n + c : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      linarith [hn0, le_of_lt hc]

    have hbound2 : (n + c) ^ comp.1.length *
          (∏ i : Fin comp.1.length, Real.rpow (comp.1.blocksFun i) p)
        ≤ (n + c) ^ comp.1.length * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k) := by
      refine mul_le_mul_of_nonneg_left hrpow' ?_
      exact pow_nonneg hncp _

    have hbound3 : (Set.ncard (T comp) : ℝ)
        ≤ (n + c) ^ comp.1.length * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k) :=
      le_trans hbound1 hbound2

    simpa [comp.2] using hbound3

  -- apply fiber bound to the sum
  have hsum : (∑ comp : ι, (Set.ncard (T comp) : ℝ))
      ≤ ∑ comp : ι, ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)) := by
    classical
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset ι))
        (f := fun comp : ι => (Set.ncard (T comp) : ℝ))
        (g := fun _comp : ι => ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)))
        (by
          intro comp hcomp
          simpa using hfiber comp))

  have hsum_const : (∑ comp : ι, ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)))
      = (Fintype.card ι : ℝ) * ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)) := by
    classical
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Finset.sum_const (s := (Finset.univ : Finset ι))
        ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)))

  have hcard_S : (Set.ncard S : ℝ) ≤
      (Fintype.card ι : ℝ) * ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)) := by
    have : (Set.ncard S : ℝ) ≤
        ∑ comp : ι, ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)) :=
      le_trans hreal hsum
    simpa [hsum_const] using this

  -- evaluate card ι using choose
  have hspos : 0 < s := Nat.succ_le_iff.mp hs
  have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 3) hd
  have hrpos : 0 < r := by
    dsimp [r]
    exact Nat.mul_pos hdpos hspos
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk

  have hcardι_nat : Fintype.card ι = Nat.choose (r - 1) (k - 1) :=
    composition_length_card_choose r k hrpos hkpos

  have hcardι_real : (Fintype.card ι : ℝ) = (Nat.choose (r - 1) (k - 1) : ℝ) := by
    exact_mod_cast hcardι_nat

  have hcard_S' : (Set.ncard S : ℝ) ≤
      (Nat.choose (r - 1) (k - 1) : ℝ) *
        ((n + c) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)) := by
    simpa [hcardι_real] using hcard_S

  -- rpow ds/k bound
  have hrpow_ds : Real.rpow ((r : ℝ) / (k : ℝ)) (p * k) ≤ (d : ℝ) ^ (p * s) := by
    have := rpow_ds_div_k_le_rpow_d_pow_s d s k p hp hs hk hks hd
    simpa [r] using this

  -- monotonicity for (n+c)^k
  have hncp : 0 ≤ (n + c : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.zero_le n)
    linarith [hn0, le_of_lt hc]

  have hnc1 : (1 : ℝ) ≤ (n + c : ℝ) := by
    have hn1_nat : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1_nat
    exact le_trans hn1 (le_add_of_nonneg_right (le_of_lt hc))

  have hks_real : (k : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hks

  have hpow_nc_rpow : (n + c : ℝ) ^ (k : ℝ) ≤ (n + c : ℝ) ^ (s : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnc1 hks_real

  have hpow_nc : (n + c : ℝ) ^ k ≤ (n + c : ℝ) ^ s := by
    have hkcast : (n + c : ℝ) ^ (k : ℝ) = (n + c : ℝ) ^ k := by
      simpa using (Real.rpow_natCast (n + c : ℝ) k)
    have hscast : (n + c : ℝ) ^ (s : ℝ) = (n + c : ℝ) ^ s := by
      simpa using (Real.rpow_natCast (n + c : ℝ) s)
    simpa [hkcast, hscast] using hpow_nc_rpow

  have hd0 : 0 ≤ (d : ℝ) := by
    exact_mod_cast (Nat.zero_le d)

  have hdpows_nonneg : 0 ≤ (d : ℝ) ^ (p * s) := by
    exact Real.rpow_nonneg hd0 (p * s)

  -- remove r/k and k from exponent bounds
  have hstep1_inner : (n + c : ℝ) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k)
      ≤ (n + c : ℝ) ^ k * (d : ℝ) ^ (p * s) := by
    refine mul_le_mul_of_nonneg_left hrpow_ds ?_
    exact pow_nonneg hncp _

  have hstep1 : (Nat.choose (r - 1) (k - 1) : ℝ) *
        ((n + c : ℝ) ^ k * Real.rpow ((r : ℝ) / (k : ℝ)) (p * k))
      ≤ (Nat.choose (r - 1) (k - 1) : ℝ) *
        ((n + c : ℝ) ^ k * (d : ℝ) ^ (p * s)) := by
    refine mul_le_mul_of_nonneg_left hstep1_inner ?_
    exact Nat.cast_nonneg _

  have hstep2_inner : (n + c : ℝ) ^ k * (d : ℝ) ^ (p * s)
      ≤ (n + c : ℝ) ^ s * (d : ℝ) ^ (p * s) := by
    exact mul_le_mul_of_nonneg_right hpow_nc hdpows_nonneg

  have hstep2 : (Nat.choose (r - 1) (k - 1) : ℝ) *
        ((n + c : ℝ) ^ k * (d : ℝ) ^ (p * s))
      ≤ (Nat.choose (r - 1) (k - 1) : ℝ) *
        ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
    refine mul_le_mul_of_nonneg_left hstep2_inner ?_
    exact Nat.cast_nonneg _

  have hcard_Sk : (Set.ncard S : ℝ) ≤
      (Nat.choose (r - 1) (k - 1) : ℝ) * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
    exact le_trans hcard_S' (le_trans hstep1 hstep2)

  -- remove k from choose
  have hd2 : 2 ≤ d := le_trans (by decide : 2 ≤ 3) hd

  have hchoose_nat : Nat.choose (r - 1) (k - 1) ≤ Nat.choose (d * s) s := by
    simpa [r] using choose_ds_pred_k_pred_le_choose_ds_s d s k hk hks hd2

  have hchoose_real : (Nat.choose (r - 1) (k - 1) : ℝ) ≤ (Nat.choose (d * s) s : ℝ) := by
    exact_mod_cast hchoose_nat

  have hB_nonneg : 0 ≤ (n + c : ℝ) ^ s * (d : ℝ) ^ (p * s) := by
    exact mul_nonneg (pow_nonneg hncp _) hdpows_nonneg

  have hstep3 : (Nat.choose (r - 1) (k - 1) : ℝ) * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s))
      ≤ (Nat.choose (d * s) s : ℝ) * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
    exact mul_le_mul_of_nonneg_right hchoose_real hB_nonneg

  have hcard_Schoose : (Set.ncard S : ℝ) ≤
      (Nat.choose (d * s) s : ℝ) * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
    exact le_trans hcard_Sk hstep3

  -- bound choose(d*s,s)
  have hchoose_exp : (Nat.choose (d * s) s : ℝ) ≤ (Real.exp 1 * d) ^ s :=
    choose_ds_le_ed_pow d s

  have hstep4 : (Nat.choose (d * s) s : ℝ) * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s))
      ≤ (Real.exp 1 * d) ^ s * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
    exact mul_le_mul_of_nonneg_right hchoose_exp hB_nonneg

  have hcard_Sbound : (Set.ncard S : ℝ) ≤ (Real.exp 1 * d) ^ s * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
    exact le_trans hcard_Schoose hstep4

  -- combine d^s * d^(p*s) into (d^(p+1))^s
  have hdne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdpos)

  have hd_mul : (d : ℝ) ^ s * (d : ℝ) ^ (p * s) = (d : ℝ) ^ (p * s + s) := by
    have h := (Real.rpow_add_natCast hdne (p * s) s).symm
    simpa [mul_comm, mul_assoc] using h

  have hexp : p * s + s = (p + 1) * s := by
    ring

  have hd_mul' : (d : ℝ) ^ s * (d : ℝ) ^ (p * s) = (d : ℝ) ^ ((p + 1) * s) := by
    simpa [hexp] using hd_mul

  have hd_comb : (d : ℝ) ^ s * (d : ℝ) ^ (p * s) = (Real.rpow (d : ℝ) (p + 1)) ^ s := by
    calc
      (d : ℝ) ^ s * (d : ℝ) ^ (p * s) = (d : ℝ) ^ ((p + 1) * s) := hd_mul'
      _ = ((d : ℝ) ^ (p + 1)) ^ s := by
        simpa using (Real.rpow_mul_natCast hd0 (p + 1) s)

  have hbound_eq : (Real.exp 1 * d) ^ s * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s))
      = (Real.exp 1 * (n + c) * Real.rpow (d : ℝ) (p + 1)) ^ s := by
    calc
      (Real.exp 1 * (d : ℝ)) ^ s * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s))
          = ((Real.exp 1) ^ s * (d : ℝ) ^ s) * ((n + c : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
              simp [mul_pow, mul_assoc]
      _ = (Real.exp 1) ^ s * (n + c : ℝ) ^ s * ((d : ℝ) ^ s * (d : ℝ) ^ (p * s)) := by
              simpa [mul_assoc] using
                (mul_mul_mul_comm ((Real.exp 1) ^ s) ((d : ℝ) ^ s) ((n + c : ℝ) ^ s) ((d : ℝ) ^ (p * s)))
      _ = (Real.exp 1) ^ s * (n + c : ℝ) ^ s * (Real.rpow (d : ℝ) (p + 1)) ^ s := by
              simp [hd_comb]
      _ = (Real.exp 1 * (n + c) * Real.rpow (d : ℝ) (p + 1)) ^ s := by
              symm
              calc
                (Real.exp 1 * (n + c) * Real.rpow (d : ℝ) (p + 1)) ^ s
                    = ((Real.exp 1 * (n + c)) * Real.rpow (d : ℝ) (p + 1)) ^ s := by
                        simp [mul_assoc]
                _ = (Real.exp 1 * (n + c)) ^ s * (Real.rpow (d : ℝ) (p + 1)) ^ s := by
                        simp [mul_pow]
                _ = ((Real.exp 1) ^ s * (n + c : ℝ) ^ s) * (Real.rpow (d : ℝ) (p + 1)) ^ s := by
                        simp [mul_pow]
                _ = (Real.exp 1) ^ s * (n + c : ℝ) ^ s * (Real.rpow (d : ℝ) (p + 1)) ^ s := by
                        simp [mul_assoc]

  have hfinalS : (Set.ncard S : ℝ) ≤ (Real.exp 1 * (n + c) * Real.rpow (d : ℝ) (p + 1)) ^ s := by
    simpa [hbound_eq] using hcard_Sbound

  simpa [S, X, r] using hfinalS

theorem ncard_rep_lists_le (n : ℕ) (hn : 2 ≤ n)
  (G : Set (FreeMonoid (Fin n)))
  (c p : ℝ) (hc : 0 < c) (hp : 0 ≤ p)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ (s d : ℕ), 1 ≤ s → 3 ≤ d →
    (Set.ncard
        { l : List (FreeMonoid (Fin n)) |
            l.length ≤ s ∧ (∀ x, x ∈ l → x ∈ (G ∪ (A n))) ∧
              (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s } : ℝ)
      ≤ (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s := by
  intro s d hs hd
  classical
  -- set of lists we want to count
  let S : Set (List (FreeMonoid (Fin n))) :=
    { l : List (FreeMonoid (Fin n)) |
        l.length ≤ s ∧ (∀ x, x ∈ l → x ∈ (G ∪ (A n))) ∧
          (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s }
  -- slices by exact length
  let Sk : ℕ → Set (List (FreeMonoid (Fin n))) := fun k =>
    { l : List (FreeMonoid (Fin n)) |
        l.length = k ∧ (∀ x, x ∈ l → x ∈ (G ∪ (A n))) ∧
          (∀ x, x ∈ l → 1 ≤ x.length) ∧ (l.prod).length = d * s }

  have hS_sub : S ⊆ ⋃ k ∈ Finset.Icc 1 s, Sk k := by
    intro l hl
    rcases hl with ⟨hls, hmem, hlenpos, hprod⟩
    have hne_nil : l ≠ [] := by
      intro hnil
      subst hnil
      have : (0:ℕ) = d * s := by
        simpa using hprod
      have hds_pos : 0 < d * s := by
        have hdpos : 0 < d := lt_of_lt_of_le (by decide : (0:ℕ) < 3) hd
        have hspos : 0 < s := lt_of_lt_of_le (by decide : (0:ℕ) < 1) hs
        exact Nat.mul_pos hdpos hspos
      exact (Nat.ne_of_lt hds_pos) this
    have hlen1 : 1 ≤ l.length := by
      have hpos : 0 < l.length := List.length_pos_of_ne_nil hne_nil
      exact Nat.succ_le_of_lt hpos
    have hk_mem : l.length ∈ Finset.Icc 1 s := by
      simp [Finset.mem_Icc, hlen1, hls]
    refine Set.mem_iUnion.2 ?_
    refine ⟨l.length, ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨hk_mem, ?_⟩
    exact ⟨rfl, hmem, hlenpos, hprod⟩

  -- a convenient finite superset for all sets we consider
  have hfin_sup : ({l : List (FreeMonoid (Fin n)) |
        l.length ≤ s ∧ (∀ x, x ∈ l → x ∈ (G ∪ (A n))) ∧ (l.prod).length = d * s}).Finite :=
    finite_rep_lists n (G ∪ (A n)) s (d * s)

  have hUnion_fin : (⋃ k ∈ Finset.Icc 1 s, Sk k).Finite := by
    -- it is a subset of the finite set from `finite_rep_lists`
    refine hfin_sup.subset ?_
    intro l hl
    rcases (Set.mem_iUnion.1 hl) with ⟨k, hk⟩
    rcases (Set.mem_iUnion.1 hk) with ⟨hkIcc, hlk⟩
    rcases hlk with ⟨hlen, hmem, hlenpos, hprod⟩
    have hks : k ≤ s := (Finset.mem_Icc.mp hkIcc).2
    have hls : l.length ≤ s := by
      simpa [hlen] using hks
    exact ⟨hls, hmem, hprod⟩

  have hcard_nat : Set.ncard S ≤ ∑ k ∈ Finset.Icc 1 s, Set.ncard (Sk k) := by
    have h1 : Set.ncard S ≤ Set.ncard (⋃ k ∈ Finset.Icc 1 s, Sk k) :=
      Set.ncard_le_ncard hS_sub hUnion_fin
    have h2 : Set.ncard (⋃ k ∈ Finset.Icc 1 s, Sk k) ≤ ∑ k ∈ Finset.Icc 1 s, Set.ncard (Sk k) :=
      Finset.set_ncard_biUnion_le (Finset.Icc 1 s) Sk
    exact le_trans h1 h2

  have hcard_real : (Set.ncard S : ℝ) ≤ ∑ k ∈ Finset.Icc 1 s, (Set.ncard (Sk k) : ℝ) := by
    exact_mod_cast hcard_nat

  -- constant appearing in the slice bound
  let Aconst : ℝ := Real.exp 1 * (n + c) * Real.rpow d (p + 1)

  -- bound each slice using the provided axiom
  have hslice : ∀ k ∈ Finset.Icc 1 s, (Set.ncard (Sk k) : ℝ) ≤ Aconst ^ s := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hks : k ≤ s := (Finset.mem_Icc.mp hk).2
    simpa [Sk, Aconst] using
      (ncard_rep_lists_slice_le n hn G c p hc hp hG s d k hs hd hk1 hks)

  have hsum_le : (∑ k ∈ Finset.Icc 1 s, (Set.ncard (Sk k) : ℝ)) ≤
      ∑ k ∈ Finset.Icc 1 s, Aconst ^ s := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hslice k hk

  have hsum_const : (∑ k ∈ Finset.Icc 1 s, Aconst ^ s) = (Finset.card (Finset.Icc 1 s) : ℝ) * (Aconst ^ s) := by
    -- sum of a constant over a finset
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

  have hmain : (Set.ncard S : ℝ) ≤ (Finset.card (Finset.Icc 1 s) : ℝ) * (Aconst ^ s) := by
    have := le_trans hcard_real hsum_le
    simpa [hsum_const] using this

  -- card(Icc 1 s) = s
  have hcard_Icc_nat : (Finset.card (Finset.Icc 1 s)) = s := by
    have : (Finset.card (Finset.Icc 1 s)) = s + 1 - 1 := by
      simpa using (Nat.card_Icc (a := 1) (b := s))
    simpa using this
  have hcard_Icc : (Finset.card (Finset.Icc 1 s) : ℝ) = s := by
    exact_mod_cast hcard_Icc_nat

  have hmain' : (Set.ncard S : ℝ) ≤ (s : ℝ) * (Aconst ^ s) := by
    simpa [hcard_Icc] using hmain

  -- use s ≤ 2^s
  have hs_pow : (s : ℝ) ≤ (2 ^ s : ℝ) := by
    exact_mod_cast (nat_le_two_pow s)

  have hA_nonneg : 0 ≤ Aconst ^ s := by
    have hA0 : 0 ≤ Aconst := by
      -- each factor is nonnegative
      have hexp : 0 ≤ Real.exp 1 := (Real.exp_nonneg 1)
      have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hnpc : 0 ≤ (n : ℝ) + c := by
        have hc0 : 0 ≤ c := le_of_lt hc
        linarith
      have hd0 : 0 ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
      have hrpow : 0 ≤ Real.rpow (d : ℝ) (p + 1) := Real.rpow_nonneg hd0 _
      have : 0 ≤ Real.exp 1 * ((n : ℝ) + c) := mul_nonneg hexp hnpc
      have : 0 ≤ (Real.exp 1 * ((n : ℝ) + c)) * Real.rpow (d : ℝ) (p + 1) :=
        mul_nonneg this hrpow
      simpa [Aconst, mul_assoc, mul_left_comm, mul_comm] using this
    exact pow_nonneg hA0 s

  have hfinal1 : (s : ℝ) * (Aconst ^ s) ≤ (2 ^ s : ℝ) * (Aconst ^ s) := by
    exact mul_le_mul_of_nonneg_right hs_pow hA_nonneg

  have hpow_two : (2 ^ s : ℝ) = (2 : ℝ) ^ s := by
    norm_cast

  have hfinal2 : (2 ^ s : ℝ) * (Aconst ^ s) = (2 * Aconst) ^ s := by
    -- use `(ab)^s = a^s b^s`
    -- and convert `(2^s : ℝ)` to `(2:ℝ)^s`
    -- (commutativity is needed to match the factors)
    simp [hpow_two, mul_pow, mul_assoc, mul_left_comm, mul_comm]

  have htemp : (Set.ncard S : ℝ) ≤ (2 ^ s : ℝ) * (Aconst ^ s) := le_trans hmain' hfinal1
  have htemp' : (Set.ncard S : ℝ) ≤ (2 * Aconst) ^ s := by
    simpa [hfinal2] using htemp

  -- unfold S and Aconst and rewrite to the required form
  simpa [S, Aconst, mul_assoc, mul_left_comm, mul_comm] using htemp'

theorem ncard_words_length_in_ball_le (n : ℕ) (hn : 2 ≤ n)
  (G : Set (FreeMonoid (Fin n)))
  (c p : ℝ) (hc : 0 < c) (hp : 0 ≤ p)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c * Real.rpow l p )) :
  ∀ (s d : ℕ), 1 ≤ s → 3 ≤ d →
    (Set.ncard { w : FreeMonoid (Fin n) | w.length = d * s ∧ w ∈ Ball s (G ∪ (A n)) }
      ≤ (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s) := by
  intro s d hs hd
  classical
  let X : Set (FreeMonoid (Fin n)) := G ∪ A n
  let r : ℕ := d * s
  let W : Set (FreeMonoid (Fin n)) :=
    { w : FreeMonoid (Fin n) | w.length = r ∧ w ∈ Ball s X }
  let Rep : Set (List (FreeMonoid (Fin n))) :=
    { l : List (FreeMonoid (Fin n)) |
        l.length ≤ s ∧ (∀ x, x ∈ l → x ∈ X) ∧ (∀ x, x ∈ l → 1 ≤ x.length) ∧
          (l.prod).length = r }

  have hRepFinite : Rep.Finite := by
    refine (finite_rep_lists n X s r).subset ?_
    intro l hl
    exact ⟨hl.1, hl.2.1, hl.2.2.2⟩

  have hWSubset : W ⊆ (fun l : List (FreeMonoid (Fin n)) => l.prod) '' Rep := by
    intro w hw
    rcases hw with ⟨hwlen, hwball⟩
    rcases Ball_exists_rep_pos_lengths n X s w hwball with ⟨l, hlen, hx, hpos, hprod⟩
    refine ⟨l, ?_, hprod⟩
    refine ⟨hlen, hx, hpos, ?_⟩
    exact (congrArg FreeMonoid.length hprod).trans hwlen

  have hWleRep_nat : Set.ncard W ≤ Set.ncard Rep := by
    have hImageFinite : ((fun l : List (FreeMonoid (Fin n)) => l.prod) '' Rep).Finite :=
      hRepFinite.image (fun l : List (FreeMonoid (Fin n)) => l.prod)
    have hWleImage : Set.ncard W ≤ Set.ncard ((fun l : List (FreeMonoid (Fin n)) => l.prod) '' Rep) :=
      Set.ncard_le_ncard hWSubset (ht := hImageFinite)
    have hImagele : Set.ncard ((fun l : List (FreeMonoid (Fin n)) => l.prod) '' Rep) ≤ Set.ncard Rep := by
      simpa using
        (Set.ncard_image_le (f := fun l : List (FreeMonoid (Fin n)) => l.prod) (s := Rep)
          (hs := hRepFinite))
    exact le_trans hWleImage hImagele

  have hWleRep : (Set.ncard W : ℝ) ≤ (Set.ncard Rep : ℝ) := by
    exact_mod_cast hWleRep_nat

  have hRepBound : (Set.ncard Rep : ℝ) ≤
      (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s := by
    simpa [Rep, X, r] using (ncard_rep_lists_le n hn G c p hc hp hG s d hs hd)

  have hWBound : (Set.ncard W : ℝ) ≤
      (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s :=
    le_trans hWleRep hRepBound

  simpa [W, X, r] using hWBound

theorem theorem_5_polynomial_density (n : ℕ) (hn : n ≥ 2)
  (G : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c * Real.rpow l p )) :
    ∀ (s d : ℕ), 1 ≤ s → (isGoodDLemma5 n c p d) →
      ¬ (Ball (d * s) (A n) ⊆ Ball s (G ∪ (A n))) := by
  classical
  intro s d hs hd
  intro hsub
  have hset : {w : FreeMonoid (Fin n) | w.length = d * s} =
      {w : FreeMonoid (Fin n) | w.length = d * s ∧ w ∈ Ball s (G ∪ (A n))} := by
    ext w
    constructor
    · intro hw
      have hwle : w.length ≤ d * s := by
        exact le_of_eq hw
      have hwball : w ∈ Ball (d * s) (A n) := mem_Ball_A_of_length_le n (d * s) w hwle
      have hwball' : w ∈ Ball s (G ∪ (A n)) := hsub hwball
      exact ⟨hw, hwball'⟩
    · intro hw
      exact hw.1

  have hineq :=
      ncard_words_length_in_ball_le n hn G c p hc hp hG s d hs hd.1
  have hbound : (Set.ncard {w : FreeMonoid (Fin n) | w.length = d * s} : ℝ) ≤
      (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s := by
    simpa [hset.symm] using hineq

  have hcardNat : Set.ncard {w : FreeMonoid (Fin n) | w.length = d * s} = n ^ (d * s) :=
    ncard_words_length_eq n (d * s)
  have hcardReal : (Set.ncard {w : FreeMonoid (Fin n) | w.length = d * s} : ℝ) = (n ^ (d * s) : ℝ) := by
    exact_mod_cast hcardNat
  have hbound' : (n ^ (d * s) : ℝ) ≤ (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s := by
    simpa [hcardReal] using hbound

  -- show strict inequality in the other direction using `hd.2`
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
    exact_mod_cast this

  have hnc : 0 < (n : ℝ) + c := by
    linarith [hnpos, hc]

  have hdpos : (0 : ℝ) < d := by
    have : (0 : ℕ) < d := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hd.1
    exact_mod_cast this

  have hdrpow : 0 < Real.rpow d (p + 1) := by
    simpa using Real.rpow_pos_of_pos hdpos (p + 1)

  have hEpos : 0 < Real.exp 1 * (n + c) * Real.rpow d (p + 1) := by
    have hexp : 0 < Real.exp 1 := by
      simpa using Real.exp_pos 1
    have hmul1 : 0 < Real.exp 1 * ((n : ℝ) + c) := mul_pos hexp hnc
    -- reassociate
    simpa [mul_assoc] using mul_pos hmul1 hdrpow

  have h2lt4 : (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) <
      (4 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) := by
    nlinarith [hEpos]

  have hd2' : (4 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) < Real.rpow n d := by
    -- `hd.2` is already `Real.rpow n d > ...`
    exact hd.2

  have hbase : (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) < Real.rpow n d :=
    lt_trans h2lt4 hd2'

  have ha0 : 0 ≤ (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) := by
    have hapos : 0 < (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      -- rewrite as 2 * (exp1*(n+c)*rpow)
      simpa [mul_assoc, mul_left_comm, mul_comm] using mul_pos h2pos hEpos
    exact le_of_lt hapos

  have hs0 : s ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) hs)

  have hpow : (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s < (Real.rpow n d) ^ s := by
    exact (pow_lt_pow_left₀ hbase ha0 (n := s) hs0)

  have hrpow_nat : Real.rpow n d = (n : ℝ) ^ d := by
    -- `Real.rpow_natCast` rewrites `x ^ (d : ℝ)`
    simpa using (Real.rpow_natCast (n : ℝ) d)

  have hrhs : (Real.rpow n d) ^ s = (n : ℝ) ^ (d * s) := by
    -- use `pow_mul` and reassociation
    simp [hrpow_nat, pow_mul, mul_assoc]

  have hrhs' : (Real.rpow n d) ^ s = (n ^ (d * s) : ℝ) := by
    -- cast nat power to real
    -- from `hrhs`, rewrite `(n:ℝ)^(d*s)`
    -- `Nat.cast_pow` gives `((n ^ (d*s) : ℕ) : ℝ) = (n:ℝ)^(d*s)`
    -- so we use its symmetry
    have hcast : (n : ℝ) ^ (d * s) = (n ^ (d * s) : ℝ) := by
      simpa using (Nat.cast_pow n (d * s) : (↑(n ^ (d * s)) : ℝ) = (n : ℝ) ^ (d * s))
    -- combine
    calc
      (Real.rpow n d) ^ s = (n : ℝ) ^ (d * s) := hrhs
      _ = (n ^ (d * s) : ℝ) := hcast

  have hpow' : (2 * Real.exp 1 * (n + c) * Real.rpow d (p + 1)) ^ s < (n ^ (d * s) : ℝ) := by
    exact lt_of_lt_of_eq hpow hrhs'

  exact (not_lt_of_ge hbound' hpow')

