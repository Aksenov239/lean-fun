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
    (∀ s : ℕ,
      (Ball s G).ncard >= Real.rpow (b : ℝ) ((s : ℝ) / (n * (b - 1)) - 1)) ∧
    (∀ r : ℕ, 2 ≤ r →
      (G ∩ (Ball r (A n))).ncard ≤ D * n * (Real.log r)) :=
    sorry

theorem theorem_2_quasi_exponential_expansion
  (n : ℕ)
  (G : Set (FreeAbelianMonoid n))
  (c q : ℝ) :
  (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) →
    (∃ (K : ℕ), ∀ (s : ℕ), (Ball s G).ncard ≤ Real.exp (K * s * (Real.log s))) :=
    sorry
theorem BallA_subset_card_le (n r : ℕ) : Ball r (A n) ⊆ {m : FreeAbelianMonoid n | m.card ≤ r} := by
  classical
  intro m hm
  rcases hm with ⟨l, hl, hx, hsum⟩
  -- lemma: if every element of a list is a singleton multiset, then the card of the sum is the length
  have hcard_sum : ∀ l : List (FreeAbelianMonoid n),
      (∀ x, x ∈ l → x ∈ A n) → (l.sum : FreeAbelianMonoid n).card = l.length := by
    intro l
    induction l with
    | nil =>
        intro _
        simp
    | cons a t ih =>
        intro hx
        have ha : a ∈ A n := hx a (by simp)
        have hx_t : ∀ x, x ∈ t → x ∈ A n := by
          intro x hxmem
          exact hx x (by simp [hxmem])
        rcases ha with ⟨i, rfl⟩
        have ih' : (t.sum : FreeAbelianMonoid n).card = t.length := ih hx_t
        -- sum of singleton multisets increases the card by 1
        simp [ih', Multiset.card_add]
  -- finish using the witness list
  have hmcard : m.card ≤ r := by
    have : (l.sum : FreeAbelianMonoid n).card ≤ r := by
      simpa [hcard_sum l hx] using hl
    simpa [hsum] using this
  simpa [Set.mem_setOf_eq] using hmcard

def Gset (n b : ℕ) : Set (FreeAbelianMonoid n) :=
  {m | ∃ (i : Fin n) (k : ℕ), m = Multiset.replicate (b ^ k) i}

def blocksAux {n : ℕ} (b : ℕ) (i : Fin n) : List ℕ → ℕ → List (FreeAbelianMonoid n)
  | [], _ => []
  | d :: ds, k => (List.replicate d (Multiset.replicate (b ^ k) i)) ++ blocksAux b i ds (k + 1)

def blocks {n : ℕ} (b : ℕ) (i : Fin n) (m : ℕ) : List (FreeAbelianMonoid n) :=
  blocksAux b i (Nat.digits b m) 0

def blocksAll {n : ℕ} (b : ℕ) (m : FreeAbelianMonoid n) : List (FreeAbelianMonoid n) :=
  (List.ofFn (fun i : Fin n => blocks b i (m.count i))).flatten

theorem blocks_mem_Gset (n b : ℕ) (i : Fin n) (m : ℕ) : ∀ x, x ∈ blocks b i m → x ∈ Gset n b := by
  intro x hx
  classical
  -- First prove the more general statement for `blocksAux`.
  have haux : ∀ (ds : List ℕ) (k : ℕ) (x : FreeAbelianMonoid n),
      x ∈ blocksAux (n := n) b i ds k → x ∈ Gset n b := by
    intro ds
    induction ds with
    | nil =>
        intro k x hx
        simpa [blocksAux] using hx
    | cons d ds ih =>
        intro k x hx
        have hx' :
            x ∈ List.replicate d (Multiset.replicate (b ^ k) i) ∨
              x ∈ blocksAux (n := n) b i ds (k + 1) := by
          exact List.mem_append.mp (by simpa [blocksAux] using hx)
        cases hx' with
        | inl hxrep =>
            rcases (List.mem_replicate.1 hxrep) with ⟨-, rfl⟩
            unfold Gset
            exact ⟨i, k, rfl⟩
        | inr hxrest =>
            exact ih (k + 1) x hxrest
  -- Now apply the auxiliary statement to `blocks`.
  unfold blocks at hx
  exact haux (Nat.digits b m) 0 x hx

theorem blocksAll_mem_Gset (n b : ℕ) (m : FreeAbelianMonoid n) : ∀ x, x ∈ blocksAll b m → x ∈ Gset n b := by
  intro x hx
  unfold blocksAll at hx
  rcases (List.mem_flatten.1 hx) with ⟨l, hl, hxl⟩
  -- hl : l ∈ List.ofFn (fun i : Fin n => blocks b i (m.count i))
  rcases (List.mem_ofFn.1 hl) with ⟨i, rfl⟩
  -- now hxl : x ∈ blocks b i (m.count i)
  exact blocks_mem_Gset n b i (m.count i) x hxl


theorem card_le_subset_BallA (n r : ℕ) : {m : FreeAbelianMonoid n | m.card ≤ r} ⊆ Ball r (A n) := by
  intro m hm
  classical
  let f : Fin n → FreeAbelianMonoid n := fun i => ({i} : Multiset (Fin n))
  let l : List (FreeAbelianMonoid n) := (m.map f).toList
  refine ⟨l, ?_, ?_, ?_⟩
  · -- length bound
    simpa [l, f] using hm
  · -- elements lie in A n
    intro x hx
    have hx' : x ∈ m.map f := by
      -- convert list membership to multiset membership
      have hx'' : x ∈ (m.map f).toList := by
        simpa [l] using hx
      exact (Multiset.mem_toList).1 hx''
    rcases (Multiset.mem_map).1 hx' with ⟨i, hi, rfl⟩
    -- show singleton is in A n
    unfold A
    exact ⟨i, rfl⟩
  · -- sum equals m
    have hsum : (m.map f).sum = m := by
      simpa [f] using (Multiset.sum_map_singleton (s := m))
    calc
      l.sum = (m.map f).toList.sum := by
        simp [l]
      _ = (m.map f).sum := by
        simpa using (Multiset.sum_toList (s := m.map f)).symm
      _ = m := hsum

theorem BallA_eq_card_le (n r : ℕ) : Ball r (A n) = {m : FreeAbelianMonoid n | m.card ≤ r} := by
  ext m
  constructor
  · intro hm
    exact (BallA_subset_card_le n r) hm
  · intro hm
    exact (card_le_subset_BallA n r) hm


theorem G_inter_BallA_ncard_bound (n b : ℕ) (hb : 2 ≤ b) : ∃ D : ℕ, ∀ r : ℕ, 2 ≤ r → (Gset n b ∩ Ball r (A n)).ncard ≤ D * n * (Real.log r) := by
  classical
  refine ⟨4, ?_⟩
  intro r hr
  -- work in ℝ
  change ((Gset n b ∩ Ball r (A n)).ncard : ℝ) ≤ (4 : ℝ) * n * Real.log r
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  -- define L = number of digits of r in base b
  let L : ℕ := (Nat.digits b r).length
  let f : (Fin n × Fin L) → FreeAbelianMonoid n := fun p =>
    Multiset.replicate (b ^ p.2.1) p.1
  have hinter_sub : Gset n b ∩ Ball r (A n) ⊆ Set.range f := by
    intro m hm
    rcases hm with ⟨hmG, hmBall⟩
    rcases hmG with ⟨i, k, rfl⟩
    have hkpow : b ^ k ≤ r := by
      have hcard : (Multiset.replicate (b ^ k) i).card ≤ r := by
        simpa [BallA_eq_card_le n r] using hmBall
      simpa [Multiset.card_replicate] using hcard
    have hk : k < L := by
      have hk' : k < (Nat.digits b r).length := (Nat.lt_digits_length_iff hb1 r).2 hkpow
      simpa [L] using hk'
    refine ⟨(i, ⟨k, hk⟩), ?_⟩
    simp [f]
  have hfinRange : (Set.range f).Finite := Set.finite_range f
  have hncard_le : (Gset n b ∩ Ball r (A n)).ncard ≤ n * L := by
    have hncard_le_range : (Gset n b ∩ Ball r (A n)).ncard ≤ (Set.range f).ncard := by
      exact Set.ncard_le_ncard hinter_sub hfinRange
    have hrange : (Set.range f).ncard ≤ n * L := by
      have h : (Set.range f).ncard ≤ (Set.univ : Set (Fin n × Fin L)).ncard := by
        simpa [Set.image_univ] using
          (Set.ncard_image_le (s := (Set.univ : Set (Fin n × Fin L))) (f := f))
      -- compute ncard of univ
      simpa [Set.ncard_univ, Fintype.card_prod, L, Nat.card_fin] using h
    exact le_trans hncard_le_range hrange
  have hncard_le_real : ((Gset n b ∩ Ball r (A n)).ncard : ℝ) ≤ (n : ℝ) * (L : ℝ) := by
    have : ((Gset n b ∩ Ball r (A n)).ncard : ℝ) ≤ (n * L : ℝ) := by
      exact_mod_cast hncard_le
    simpa [Nat.cast_mul] using this
  -- logarithmic bound for L
  have hr0 : r ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hr)
  have hL_eq : L = Nat.log b r + 1 := by
    simpa [L] using Nat.digits_len b r hb1 hr0
  have hbposNat : 0 < b := lt_trans (by decide : (0 : ℕ) < 1) hb1
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbposNat
  have hlogb_pos : 0 < Real.log (b : ℝ) := by
    have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
    exact Real.log_pos this
  have hpow_log : (b : ℝ) ^ Nat.log b r ≤ (r : ℝ) := by
    have hnat : b ^ Nat.log b r ≤ r := Nat.pow_log_le_self b (x := r) hr0
    exact_mod_cast hnat
  have hmul_log : (Nat.log b r : ℝ) * Real.log (b : ℝ) ≤ Real.log r := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.le_log_of_pow_le (n := Nat.log b r) hbpos hpow_log)
  have hlogNat : (Nat.log b r : ℝ) ≤ Real.log r / Real.log (b : ℝ) := by
    exact (le_div_iff₀ hlogb_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul_log)
  have hL_le1 : (L : ℝ) ≤ Real.log r / Real.log (b : ℝ) + 1 := by
    have h := add_le_add_right hlogNat 1
    simpa [hL_eq, Nat.cast_add, Nat.cast_one] using h
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.log_pos this
  have hlogr_nonneg : 0 ≤ Real.log r := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (r : ℝ) := by
      have : (1 : ℕ) ≤ r := le_trans (by decide : (1 : ℕ) ≤ 2) hr
      exact_mod_cast this
    exact this
  have hlog2_le_logb : Real.log (2 : ℝ) ≤ Real.log (b : ℝ) := by
    have h2le : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.log_le_log h2pos h2le
  have hdiv : Real.log r / Real.log (b : ℝ) ≤ Real.log r / Real.log (2 : ℝ) := by
    exact div_le_div_of_nonneg_left hlogr_nonneg hlog2_pos hlog2_le_logb
  have hL_le2 : (L : ℝ) ≤ Real.log r / Real.log (2 : ℝ) + 1 := by
    have h := add_le_add_right hdiv 1
    have h' : Real.log r / Real.log (b : ℝ) + 1 ≤ Real.log r / Real.log (2 : ℝ) + 1 := by
      simpa [add_assoc, add_comm, add_left_comm] using h
    exact le_trans hL_le1 h'
  -- now bound `log r / log 2 + 1` by `4 * log r`
  have hx_ge1 : (1 : ℝ) ≤ Real.log r / Real.log (2 : ℝ) := by
    have h2le : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hlog2_le : Real.log (2 : ℝ) ≤ Real.log r := Real.log_le_log h2pos h2le
    have : Real.log (2 : ℝ) / Real.log (2 : ℝ) ≤ Real.log r / Real.log (2 : ℝ) := by
      exact div_le_div_of_nonneg_right hlog2_le (le_of_lt hlog2_pos)
    simpa [div_self (ne_of_gt hlog2_pos)] using this
  have h_add1 : Real.log r / Real.log (2 : ℝ) + 1 ≤ 2 * (Real.log r / Real.log (2 : ℝ)) := by
    have h := add_le_add_left hx_ge1 (Real.log r / Real.log (2 : ℝ))
    simpa [two_mul, add_assoc, add_comm, add_left_comm] using h
  have hlog2_gt_half : (1 / 2 : ℝ) < Real.log (2 : ℝ) := by
    have hhalf : (1 / 2 : ℝ) < (0.6931471803 : ℝ) := by norm_num
    exact lt_trans hhalf Real.log_two_gt_d9
  have h2_div : (2 : ℝ) / Real.log (2 : ℝ) ≤ 4 := by
    have hlt : (2 : ℝ) < (4 : ℝ) * Real.log (2 : ℝ) := by
      nlinarith [hlog2_gt_half]
    have hle : (2 : ℝ) ≤ (4 : ℝ) * Real.log (2 : ℝ) := le_of_lt hlt
    exact (div_le_iff₀ hlog2_pos).2 hle
  have hmul2 : 2 * (Real.log r / Real.log (2 : ℝ)) ≤ 4 * Real.log r := by
    have h := mul_le_mul_of_nonneg_right h2_div hlogr_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hlog_bound : Real.log r / Real.log (2 : ℝ) + 1 ≤ 4 * Real.log r := le_trans h_add1 hmul2
  have hL_log : (L : ℝ) ≤ 4 * Real.log r := le_trans hL_le2 hlog_bound
  have hmul : (n : ℝ) * (L : ℝ) ≤ (4 : ℝ) * n * Real.log r := by
    have h := mul_le_mul_of_nonneg_left hL_log (by positivity : 0 ≤ (n : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  exact le_trans hncard_le_real hmul

theorem length_blocksAll_eq_sum (n b : ℕ) (m : FreeAbelianMonoid n) : (blocksAll b m).length = ∑ i : Fin n, (blocks b i (m.count i)).length := by
  classical
  -- Unfold and compute length of `flatten`.
  simp [blocksAll, List.length_flatten, List.map_ofFn, List.sum_ofFn]

theorem length_blocks_le (n b : ℕ) (i : Fin n) (m : ℕ) (hb : 2 ≤ b) : (blocks b i m).length ≤ (b - 1) * (Nat.digits b m).length := by
  classical
  unfold blocks
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have haux :
      ∀ ds : List ℕ,
        ∀ k : ℕ,
          (∀ d ∈ ds, d < b) →
            (blocksAux (n := n) b i ds k).length ≤ (b - 1) * ds.length := by
    intro ds
    induction ds with
    | nil =>
        intro k hds
        simp [blocksAux]
    | cons d ds ih =>
        intro k hds
        have hdlt : d < b := hds d (by simp)
        have htail : ∀ d' ∈ ds, d' < b := by
          intro d' hd'
          exact hds d' (by simp [hd'])
        have hdle : d ≤ b - 1 := by
          exact Order.le_sub_one_of_lt hdlt
        have hlenTail :
            (blocksAux (n := n) b i ds (k + 1)).length ≤ (b - 1) * ds.length :=
          ih (k := k + 1) htail
        have hsum :
            d + (blocksAux (n := n) b i ds (k + 1)).length ≤ (b - 1) + (b - 1) * ds.length := by
          exact Nat.add_le_add hdle hlenTail
        calc
          (blocksAux (n := n) b i (d :: ds) k).length
              = d + (blocksAux (n := n) b i ds (k + 1)).length := by
                simp [blocksAux, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          _ ≤ (b - 1) + (b - 1) * ds.length := hsum
          _ = (b - 1) * (ds.length + 1) := by
                simp [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          _ = (b - 1) * (List.length (d :: ds)) := by
                simp
  refine haux (Nat.digits b m) 0 ?_
  intro d hd
  exact Nat.digits_lt_base hb1 hd


theorem length_blocksAll_le (n b r : ℕ) (m : FreeAbelianMonoid n) (hb : 2 ≤ b) (hm : m.card ≤ r) : (blocksAll b m).length ≤ n * (b - 1) * (Nat.digits b r).length := by
  classical
  -- rewrite `blocksAll` length as a sum
  have hlen : (blocksAll b m).length = ∑ i : Fin n, (blocks b i (m.count i)).length :=
    length_blocksAll_eq_sum n b m
  -- constant bound for each summand
  set C : ℕ := (b - 1) * (Nat.digits b r).length
  have hterm : ∀ i : Fin n, (blocks b i (m.count i)).length ≤ C := by
    intro i
    have hblocks : (blocks b i (m.count i)).length ≤ (b - 1) * (Nat.digits b (m.count i)).length := by
      simpa using (length_blocks_le n b i (m.count i) hb)
    have hci : m.count i ≤ m.card := by
      simpa using (Multiset.count_le_card i m)
    have hcir : m.count i ≤ r := le_trans hci hm
    have hd : (Nat.digits b (m.count i)).length ≤ (Nat.digits b r).length := by
      simpa using Nat.le_digits_len_le b (m.count i) r hcir
    have hmul : (b - 1) * (Nat.digits b (m.count i)).length ≤ C := by
      -- multiply both sides of `hd` by `b-1`
      simpa [C, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_left (b - 1) hd
    exact le_trans hblocks hmul
  -- bound the sum by summing the pointwise bounds
  have hsum : (∑ i : Fin n, (blocks b i (m.count i)).length) ≤ ∑ _i : Fin n, C := by
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa using hterm i
  -- finish
  -- rewrite everything and evaluate the sum of a constant
  calc
    (blocksAll b m).length
        = ∑ i : Fin n, (blocks b i (m.count i)).length := hlen
    _ ≤ ∑ _i : Fin n, C := hsum
    _ = n * C := by
      simpa using (Finset.sum_const_nat (f := fun _ : Fin n => C))
    _ = n * (b - 1) * (Nat.digits b r).length := by
      simp [C, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]


theorem sum_blocksAux (n b : ℕ) (i : Fin n) (ds : List ℕ) (k : ℕ) : (blocksAux (n:=n) b i ds k).sum = Multiset.replicate (Nat.ofDigits b ds * (b ^ k)) i := by
  induction ds generalizing k with
  | nil =>
      simp [blocksAux]
  | cons d ds ih =>
      -- unfold and reduce to replicate arithmetic
      simp [blocksAux, List.sum_append, List.sum_replicate, ih, Multiset.nsmul_replicate,
        Nat.ofDigits_cons, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
        Nat.add_mul, Nat.mul_add]
      -- combine replicates
      rw [Multiset.replicate_add]
      

theorem sum_blocks (n b : ℕ) (i : Fin n) (m : ℕ) : (blocks b i m).sum = Multiset.replicate m i := by
  unfold blocks
  rw [sum_blocksAux (n:=n) (b:=b) (i:=i) (ds:=Nat.digits b m) (k:=0)]
  simp [Nat.ofDigits_digits]


theorem replicate_mem_Ball_Gset (n b : ℕ) (i : Fin n) (m R : ℕ) (hb : 2 ≤ b) (hm : m ≤ R) :
  Multiset.replicate m i ∈ Ball ((b - 1) * (Nat.digits b R).length) (Gset n b) := by
  classical
  refine ⟨blocks (n := n) b i m, ?_⟩
  refine ⟨?_, ?_⟩
  ·
    have hlen₁ : (blocks (n := n) b i m).length ≤ (b - 1) * (Nat.digits b m).length :=
      length_blocks_le n b i m hb
    have hdigits : (Nat.digits b m).length ≤ (Nat.digits b R).length :=
      Nat.le_digits_len_le b m R hm
    have hmul : (b - 1) * (Nat.digits b m).length ≤ (b - 1) * (Nat.digits b R).length :=
      Nat.mul_le_mul_left (b - 1) hdigits
    exact le_trans hlen₁ hmul
  ·
    refine ⟨?_, ?_⟩
    ·
      intro x hx
      exact blocks_mem_Gset n b i m x hx
    ·
      simpa using sum_blocks n b i m

theorem sum_replicate_count_univ (n : ℕ) (m : Multiset (Fin n)) : (∑ i : Fin n, Multiset.replicate (m.count i) i) = m := by
  classical
  ext a
  simp [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq]

theorem sum_blocksAll (n b : ℕ) (m : FreeAbelianMonoid n) : (blocksAll b m).sum = m := by
  classical
  -- Unfold the definition of `blocksAll` and rewrite the sum over `flatten`.
  simp [blocksAll, List.sum_flatten, List.map_ofFn, List.sum_ofFn, sum_blocks, sum_replicate_count_univ]

theorem BallA_subset_BallG (n b r s : ℕ) (hb : 2 ≤ b) : (2 ≤ r) ∧ (s ≥ n * (b - 1) * ((Real.log r) / (Real.log b) + 1)) → (Ball r (A n)) ⊆ (Ball s (Gset n b)) := by
  classical
  intro hs
  intro m hm
  rcases hs with ⟨hr2, hs⟩
  have hmcard : m.card ≤ r := by
    simpa [BallA_eq_card_le] using hm
  let L : List (FreeAbelianMonoid n) := blocksAll b m
  have hsum : L.sum = m := by
    simpa [L] using sum_blocksAll n b m
  have hmem : ∀ x, x ∈ L → x ∈ Gset n b := by
    intro x hx
    have hx' : x ∈ blocksAll b m := by
      simpa [L] using hx
    exact blocksAll_mem_Gset n b m x hx'
  have hlenR : L.length ≤ n * (b - 1) * (Nat.digits b r).length := by
    simpa [L] using length_blocksAll_le n b r m hb hmcard

  have hbound : n * (b - 1) * (Nat.digits b r).length ≤ s := by
    have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hr0 : r ≠ 0 := by
      have : 0 < r := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hr2
      exact Nat.ne_of_gt this
    have hdigits : (Nat.digits b r).length = Nat.log b r + 1 := by
      simpa using Nat.digits_len b r hb1 hr0
    have hlog : (Nat.log b r : ℝ) ≤ Real.log r / Real.log b := by
      calc
        (Nat.log b r : ℝ) ≤ Real.logb (b : ℝ) (r : ℝ) := by
          simpa using (Real.natLog_le_logb r b)
        _ = Real.log r / Real.log b := by
          simpa using (Real.log_div_log (b := (b : ℝ)) (x := (r : ℝ))).symm
    have hdigits_le : ((Nat.digits b r).length : ℝ) ≤ Real.log r / Real.log b + 1 := by
      have hdigits_real : ((Nat.digits b r).length : ℝ) = (Nat.log b r : ℝ) + 1 := by
        exact_mod_cast hdigits
      calc
        ((Nat.digits b r).length : ℝ) = (Nat.log b r : ℝ) + 1 := hdigits_real
        _ ≤ Real.log r / Real.log b + 1 := by
          exact add_le_add_left hlog 1

    have hb1le : (1 : ℕ) ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
    have hbcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - (1 : ℝ) := by
      simpa using (Nat.cast_sub hb1le : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - (1 : ℕ))

    have hprod : (n * (b - 1) * (Nat.digits b r).length : ℝ)
        ≤ (n : ℝ) * ((b : ℝ) - 1) * (Real.log r / Real.log b + 1) := by
      have hmul' : (n : ℝ) * ((b - 1 : ℕ) : ℝ) * ((Nat.digits b r).length : ℝ)
          ≤ (n : ℝ) * ((b - 1 : ℕ) : ℝ) * (Real.log r / Real.log b + 1) := by
        have hconst_nonneg : 0 ≤ (n : ℝ) * ((b - 1 : ℕ) : ℝ) := by
          positivity
        exact mul_le_mul_of_nonneg_left hdigits_le hconst_nonneg
      -- rewrite (b - 1) casts
      have hbcast' : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        simpa using hbcast
      simpa [mul_assoc, mul_left_comm, mul_comm, Nat.cast_mul, hbcast'] using hmul'

    have hsReal : (n : ℝ) * ((b : ℝ) - 1) * (Real.log r / Real.log b + 1) ≤ (s : ℝ) := by
      have hbcast' : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        simpa using hbcast
      -- `hs` already has the right form but might use nat subtraction; normalize
      simpa [ge_iff_le, hbcast', mul_assoc, mul_left_comm, mul_comm, Nat.cast_mul] using hs

    have hN_real : (n * (b - 1) * (Nat.digits b r).length : ℝ) ≤ (s : ℝ) := le_trans hprod hsReal
    exact_mod_cast hN_real

  have hlen : L.length ≤ s := le_trans hlenR hbound
  refine ⟨L, ?_⟩
  exact ⟨hlen, hmem, hsum⟩

theorem lemma_1_balls_inclusion (n b : ℕ) (hb : 2 ≤ b) :
  ∃ (G : Set (FreeAbelianMonoid n)) (D : ℕ),
    (∀ (r s : ℕ), (2 ≤ r) ∧ (s ≥ n * (b - 1) * ((Real.log r) / (Real.log b) + 1)) →
      (Ball r (A n)) ⊆ (Ball s G)) ∧
    (∀ r : ℕ, 2 ≤ r →
      (G ∩ (Ball r (A n))).ncard ≤ D * n * (Real.log r)) := by
  classical
  rcases G_inter_BallA_ncard_bound n b hb with ⟨D, hD⟩
  refine ⟨Gset n b, D, ?_, ?_⟩
  · intro r s hrs
    exact BallA_subset_BallG n b r s hb hrs
  · intro r hr
    simpa using hD r hr


