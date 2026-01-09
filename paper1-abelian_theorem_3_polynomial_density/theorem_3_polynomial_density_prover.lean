import Mathlib

open scoped BigOperators

abbrev FreeAbelianMonoid (n : ℕ) := Multiset (Fin n)

def A (n : ℕ) : Set (FreeAbelianMonoid n) :=
  { {i} | i : Fin n}

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) : Set (FreeAbelianMonoid n) :=
  {m | ∃ l : List (FreeAbelianMonoid n), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

theorem Ball_A_iff_card_le {n : ℕ} (r : ℕ) (m : FreeAbelianMonoid n) :
  m ∈ Ball r (A n) ↔ m.card ≤ r := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hlr, hmem, hsum⟩
    -- card of sum equals length when all elements are singletons
    have hcard_sum_len : ∀ l : List (FreeAbelianMonoid n),
        (∀ x, x ∈ l → x ∈ A n) → (l.sum).card = l.length := by
      intro l
      induction l with
      | nil =>
          intro h
          simp
      | cons a t ih =>
          intro h
          have haA : a ∈ A n := h a (by simp)
          rcases haA with ⟨i, rfl⟩
          have ht : ∀ x, x ∈ t → x ∈ A n := by
            intro x hx
            exact h x (by simp [hx])
          simpa [List.sum_cons, Multiset.card_add, ih ht]
    have hmcard_eq : m.card = l.length := by
      calc
        m.card = (l.sum).card := by
          simpa using (congrArg Multiset.card hsum).symm
        _ = l.length := hcard_sum_len l hmem
    -- conclude
    have : l.length ≤ r := hlr
    --
    simpa [hmcard_eq] using this
  · intro hmcard
    -- construct witness list
    let l : List (FreeAbelianMonoid n) := (m.map (fun i : Fin n => ({i} : FreeAbelianMonoid n))).toList
    refine ⟨l, ?_, ?_, ?_⟩
    · -- length bound
      have hl : l.length = m.card := by
        simp [l]
      simpa [hl] using hmcard
    · -- all elements in A
      intro x hx
      have hx' : x ∈ m.map (fun i : Fin n => ({i} : FreeAbelianMonoid n)) := by
        simpa [l] using (Multiset.mem_toList.mp hx)
      rcases (Multiset.mem_map.mp hx') with ⟨i, hi, rfl⟩
      exact ⟨i, rfl⟩
    · -- sum equals m
      simp [l]


theorem Ball_add {n : ℕ} {R S : ℕ} {X : Set (FreeAbelianMonoid n)} {a b : FreeAbelianMonoid n} :
  a ∈ Ball R X → b ∈ Ball S X → (a + b) ∈ Ball (R + S) X := by
  intro ha hb
  rcases ha with ⟨l₁, hl₁len, hl₁X, hl₁sum⟩
  rcases hb with ⟨l₂, hl₂len, hl₂X, hl₂sum⟩
  refine ⟨l₁ ++ l₂, ?_, ?_, ?_⟩
  · -- length bound
    simpa [List.length_append] using (Nat.add_le_add hl₁len hl₂len)
  · -- membership in X
    intro x hx
    rcases (List.mem_append.mp hx) with hx | hx
    · exact hl₁X x hx
    · exact hl₂X x hx
  · -- sum
    simpa [List.sum_append, hl₁sum, hl₂sum, add_assoc, add_comm, add_left_comm]

theorem Ball_finset_sum {n : ℕ} {X : Set (FreeAbelianMonoid n)} (R : ℕ) (s : Finset (Fin n)) (f : Fin n → FreeAbelianMonoid n)
  (hf : ∀ i ∈ s, f i ∈ Ball R X) :
  (∑ i ∈ s, f i) ∈ Ball (s.card * R) X := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro hf
    simp [Ball]
  · intro a s ha ih
    intro hf
    have hfa : f a ∈ Ball R X := hf a (by simp)
    have hfs : ∀ i ∈ s, f i ∈ Ball R X := by
      intro i hi
      exact hf i (Finset.mem_insert_of_mem hi)
    have hsums : (∑ i ∈ s, f i) ∈ Ball (s.card * R) X := ih hfs
    have hsum : (f a + ∑ i ∈ s, f i) ∈ Ball (R + s.card * R) X :=
      Ball_add hfa hsums
    have hsum' : (∑ i ∈ insert a s, f i) ∈ Ball (R + s.card * R) X := by
      simpa [Finset.sum_insert, ha, add_assoc, add_comm, add_left_comm] using hsum
    have hrad : R + s.card * R = (insert a s).card * R := by
      calc
        R + s.card * R = s.card * R + R := by ac_rfl
        _ = s.card.succ * R := by
          simpa using (Nat.succ_mul s.card R).symm
        _ = (insert a s).card * R := by
          simp [Finset.card_insert_of_not_mem, ha, Nat.succ_eq_add_one]
    simpa [hrad] using hsum'

theorem Ball_mono {n : ℕ} {R S : ℕ} {X : Set (FreeAbelianMonoid n)} (hRS : R ≤ S) :
  Ball R X ⊆ Ball S X := by
  intro m hm
  rcases hm with ⟨l, hlR, hX, hsum⟩
  refine ⟨l, le_trans hlR hRS, hX, hsum⟩


def Gpow (n k : ℕ) : Set (FreeAbelianMonoid n) :=
  {m | ∃ (i : Fin n) (t : ℕ), 1 ≤ t ∧ m = (t ^ k) • ({i} : FreeAbelianMonoid n)}

def isWarring (k : ℕ) (n : ℕ) : Prop :=
  ∀ x : ℕ, ∃ l : List ℕ, l.length ≤ n ∧ (l.map (fun (y : ℕ) => y ^ k)).sum = x

theorem count_nsmul_singleton_mem_Ball_Gpow (n k s : ℕ) (hk : k ≥ 2) (hs : isWarring k s) (i : Fin n) (a : ℕ) :
  (a • ({i} : FreeAbelianMonoid n)) ∈ Ball s (Gpow n k) := by
  classical
  rcases hs a with ⟨l, hl_len, hl_sum⟩
  let l' : List ℕ := l.filter (fun y : ℕ => y ≠ 0)
  let L : List (FreeAbelianMonoid n) := l'.map (fun y : ℕ => (y ^ k) • ({i} : FreeAbelianMonoid n))
  refine ⟨L, ?_, ?_, ?_⟩

  · -- length
    have hfilter : l'.length ≤ l.length := by
      simpa [l'] using (List.filter_sublist (p := fun y : ℕ => y ≠ 0) (l := l)).length_le
    have hlen' : l'.length ≤ s := le_trans hfilter hl_len
    simpa [L] using hlen'

  · -- membership in `Gpow`
    intro x hx
    rcases List.mem_map.1 hx with ⟨y, hy, rfl⟩
    have hydec : decide (y ≠ 0) = true := (List.mem_filter.1 hy).2
    have hyne0 : y ≠ 0 := (Bool.decide_iff (p := y ≠ 0)).1 hydec
    have hy1 : 1 ≤ y := (Nat.one_le_iff_ne_zero).2 hyne0
    refine ⟨i, y, hy1, rfl⟩

  · -- sum computation
    have hk0 : k ≠ 0 := by
      have : (0 : ℕ) < k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk
      exact Nat.ne_of_gt this

    -- sum over the zero terms is zero
    have hsum_zero : ((l.filter (fun y : ℕ => y = 0)).map (fun y : ℕ => y ^ k)).sum = 0 := by
      apply List.sum_eq_zero
      intro z hz
      rcases List.mem_map.1 hz with ⟨y, hy, rfl⟩
      have hydec : decide (y = 0) = true := (List.mem_filter.1 hy).2
      have hy0 : y = 0 := (Bool.decide_iff (p := y = 0)).1 hydec
      subst hy0
      simp [hk0]

    -- hence the filtered sum of powers is still `a`
    have hsum_l' : (l'.map (fun y : ℕ => y ^ k)).sum = a := by
      have h := List.sum_map_filter_add_sum_map_filter_not (l := l)
        (p := fun y : ℕ => y = 0) (f := fun y : ℕ => y ^ k)
      have h' : ((l.filter (fun y : ℕ => y = 0)).map (fun y : ℕ => y ^ k)).sum +
            ((l.filter fun y : ℕ => ¬ y = 0).map (fun y : ℕ => y ^ k)).sum = a := by
        simpa [hl_sum] using h
      have h'' : 0 + ((l.filter fun y : ℕ => ¬ y = 0).map (fun y : ℕ => y ^ k)).sum = a := by
        simpa [hsum_zero] using h'
      have h''' : ((l.filter fun y : ℕ => ¬ y = 0).map (fun y : ℕ => y ^ k)).sum = a := by
        simpa using h''
      simpa [l'] using h'''

    -- factor out `{i}`
    have hsum_L : L.sum = ((l'.map (fun y : ℕ => y ^ k)).sum) • ({i} : FreeAbelianMonoid n) := by
      unfold L
      induction l' with
      | nil => simp
      | cons y ys ih =>
          simp [ih, add_nsmul]

    simpa [hsum_L, hsum_l']


theorem Gpow_expansion (n k s : ℕ) (hk : k ≥ 2) (hs : isWarring k s) :
  ∀ r : ℕ, Ball r (A n) ⊆ Ball (n * s) (Gpow n k) := by
  intro r
  intro m hm
  classical
  -- Choose a Waring representation for each multiplicity
  choose w hwlen hwsum using fun i : Fin n => hs (m.count i)

  -- Nonzero predicate (as Bool) so we can filter away zeros
  let p : ℕ → Bool := fun t => !decide (t = 0)
  let w' : Fin n → List ℕ := fun i => (w i).filter p

  -- Turn a Waring list into a list of elements of `Gpow`
  let Li : Fin n → List (FreeAbelianMonoid n) :=
    fun i => (w' i).map (fun t => (t ^ k) • ({i} : FreeAbelianMonoid n))

  -- Enumerate the support of `m`
  let I : List (Fin n) := m.toFinset.toList

  refine ⟨I.flatMap Li, ?_, ?_, ?_⟩

  · -- length bound
    have hw'_len (i : Fin n) : (w' i).length ≤ s := by
      have hEq := (List.length_eq_length_filter_add (l := w i) (f := p))
      have hle : ((w i).filter p).length ≤
          ((w i).filter p).length + ((w i).filter (!p ·)).length :=
        Nat.le_add_right _ _
      have hfilter_le : ((w i).filter p).length ≤ (w i).length :=
        le_trans hle (le_of_eq hEq.symm)
      exact le_trans hfilter_le (hwlen i)

    have hLi_len (i : Fin n) : (Li i).length ≤ s := by
      dsimp [Li]
      simpa [w', p] using hw'_len i

    have hlen_flatMap : (I.flatMap Li).length ≤ I.length * s := by
      induction I with
      | nil =>
          simp [List.flatMap]
      | cons a I ih =>
          have h := Nat.add_le_add (hLi_len a) ih
          simpa [List.flatMap, List.length_append, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using h

    have hIlen : I.length = m.toFinset.card := by
      simpa [I] using (Finset.length_toList (s := m.toFinset))

    have hcard : m.toFinset.card ≤ n := by
      simpa using
        (Finset.card_le_univ (s := m.toFinset) : m.toFinset.card ≤ Fintype.card (Fin n))

    have hIle : I.length ≤ n := by
      rw [hIlen]
      exact hcard

    have hlen2 : I.length * s ≤ n * s := Nat.mul_le_mul_right s hIle
    exact le_trans hlen_flatMap hlen2

  · -- membership in `Gpow`
    intro x hx

    have hLi_mem (i : Fin n) : ∀ x, x ∈ Li i → x ∈ Gpow n k := by
      intro x hx
      dsimp [Li] at hx
      rcases List.mem_map.1 hx with ⟨t, ht, rfl⟩
      have ht0 : t ≠ 0 := by
        have hp : p t := List.of_mem_filter ht
        simpa [p] using hp
      refine ⟨i, t, (Nat.one_le_iff_ne_zero).2 ht0, rfl⟩

    rcases List.mem_flatMap.1 hx with ⟨i, hiI, hxi⟩
    exact hLi_mem i x hxi

  · -- sum equals `m`
    have hk0 : k ≠ 0 := by
      have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
      exact Nat.ne_of_gt hkpos

    -- Removing zeros doesn't change the sum of k-th powers
    have hfilter_pow_sum (L : List ℕ) :
        ((L.filter p).map (fun t => t ^ k)).sum = (L.map (fun t => t ^ k)).sum := by
      induction L with
      | nil => simp [p]
      | cons t L ih =>
          by_cases ht : t = 0
          · subst ht
            simp [p, ih, hk0]
          ·
            have hp : p t = true := by
              simp [p, ht]
            simp [List.filter, hp, ih, p]

    have hw'_pow_sum (i : Fin n) : ((w' i).map (fun t => t ^ k)).sum = m.count i := by
      calc
        ((w' i).map (fun t => t ^ k)).sum = ((w i).map (fun t => t ^ k)).sum := by
          simpa [w', p] using (hfilter_pow_sum (L := w i))
        _ = m.count i := hwsum i

    -- Factor `• {i}` out of the list sum
    have hsum_nsmul_single (i : Fin n) (L : List ℕ) :
        (L.map (fun t => (t ^ k) • ({i} : FreeAbelianMonoid n))).sum =
          ((L.map (fun t => t ^ k)).sum) • ({i} : FreeAbelianMonoid n) := by
      induction L with
      | nil => simp
      | cons t L ih =>
          simp [ih, add_nsmul]

    have hLi_sum (i : Fin n) : (Li i).sum = (m.count i) • ({i} : FreeAbelianMonoid n) := by
      dsimp [Li]
      calc
        (List.map (fun t => (t ^ k) • ({i} : FreeAbelianMonoid n)) (w' i)).sum =
            ((List.map (fun t => t ^ k) (w' i)).sum) • ({i} : FreeAbelianMonoid n) := by
          simpa using (hsum_nsmul_single i (w' i))
        _ = (m.count i) • ({i} : FreeAbelianMonoid n) := by
          simpa [hw'_pow_sum i]

    -- Sum of the flatMap is the sum of the sums
    have hsum_flatMap : (I.flatMap Li).sum = (I.map (List.sum ∘ Li)).sum := by
      induction I with
      | nil => simp [List.flatMap]
      | cons a I ih =>
          simp [List.flatMap, ih, List.sum_append, Function.comp, add_assoc, add_left_comm, add_comm]

    have hsum_map : (I.map (List.sum ∘ Li)).sum =
        (I.map (fun i => (m.count i) • ({i} : FreeAbelianMonoid n))).sum := by
      induction I with
      | nil => simp [Function.comp]
      | cons a I ih =>
          simp [Function.comp, hLi_sum, ih]

    have hlist_finset :
        (I.map (fun i => (m.count i) • ({i} : FreeAbelianMonoid n))).sum =
          ∑ i ∈ m.toFinset, (m.count i) • ({i} : FreeAbelianMonoid n) := by
      simpa [I] using
        (Finset.sum_toList (s := m.toFinset)
          (f := fun i : Fin n => (m.count i) • ({i} : FreeAbelianMonoid n))).symm

    calc
      (I.flatMap Li).sum = (I.map (List.sum ∘ Li)).sum := hsum_flatMap
      _ = (I.map (fun i => (m.count i) • ({i} : FreeAbelianMonoid n))).sum := hsum_map
      _ = ∑ i ∈ m.toFinset, (m.count i) • ({i} : FreeAbelianMonoid n) := hlist_finset
      _ = m := by
        simpa using (Multiset.toFinset_sum_count_nsmul_eq m)

theorem ncard_pow_le_rpow (k r : ℕ) (hk : k ≥ 2) :
  ({t : ℕ | 1 ≤ t ∧ t ^ k ≤ r} : Set ℕ).ncard ≤ Real.rpow r ((1 : ℝ) / k) := by
  classical
  let S : Set ℕ := {t : ℕ | 1 ≤ t ∧ t ^ k ≤ r}
  let x : ℝ := Real.rpow (r : ℝ) ((1 : ℝ) / k)
  let m : ℕ := Nat.floor x
  have hx0 : 0 ≤ x := by
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.zero_le r)
    simpa [x] using (Real.rpow_nonneg hr0 ((1 : ℝ) / k))
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hk
  have hkne0 : k ≠ 0 := ne_of_gt hkpos

  have hSsub : S ⊆ Set.Icc 1 m := by
    intro t ht
    rcases ht with ⟨ht1, htPow⟩
    refine ⟨ht1, ?_⟩
    have htPowR : ((t : ℝ) ^ k) ≤ (r : ℝ) := by
      have : ((t ^ k : ℝ) ≤ (r : ℝ)) := by
        exact_mod_cast htPow
      simpa [Nat.cast_pow] using this
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (Nat.zero_le t)
    have ht0' : (0 : ℝ) ≤ (t : ℝ) ^ k := by
      exact pow_nonneg ht0 k
    have hk0 : (0 : ℝ) ≤ (1 : ℝ) / k := by
      exact div_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le k))
    have htrpow : ((t : ℝ) ^ k) ^ ((1 : ℝ) / k) ≤ (r : ℝ) ^ ((1 : ℝ) / k) :=
      Real.rpow_le_rpow ht0' htPowR hk0
    have hpow : ((t : ℝ) ^ k) ^ ((k : ℝ)⁻¹) = (t : ℝ) := by
      simpa using (Real.pow_rpow_inv_natCast ht0 hkne0)
    have ht_le_x : (t : ℝ) ≤ x := by
      have : ((t : ℝ) ^ k) ^ ((k : ℝ)⁻¹) ≤ x := by
        simpa [x, one_div] using htrpow
      simpa [hpow] using this
    have ht_le_m : t ≤ m := by
      exact_mod_cast (Nat.le_floor ht_le_x)
    exact ht_le_m

  have hcard : S.ncard ≤ (Set.Icc 1 m : Set ℕ).ncard := by
    exact Set.ncard_le_ncard hSsub (Set.finite_Icc (a := (1 : ℕ)) (b := m))

  have hIcc : (Set.Icc 1 m : Set ℕ).ncard = m := by
    have h1 : (Set.Icc 1 m : Set ℕ).ncard = (Finset.Icc 1 m).card := by
      -- ncard of the set is the card of the corresponding finset
      simpa [Finset.coe_Icc] using (Set.ncard_coe_finset (Finset.Icc (1 : ℕ) m))
    -- compute card of finset interval
    have h2 : (Finset.Icc (1 : ℕ) m).card = m + 1 - 1 := by
      simpa using (Nat.card_Icc (a := (1 : ℕ)) (b := m))
    -- simplify
    simpa [h1, h2]

  have hm_le_x : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hS_le_m : (S.ncard : ℝ) ≤ m := by
    have : (S.ncard : ℝ) ≤ (Set.Icc 1 m : Set ℕ).ncard := by
      exact_mod_cast hcard
    simpa [hIcc] using this
  exact le_trans hS_le_m hm_le_x


theorem Gpow_density (n k : ℕ) (hk : k ≥ 2) :
  ∀ r : ℕ, (Gpow n k ∩ Ball r (A n)).ncard ≤ n * (Real.rpow r ((1 : ℝ) / k)) := by
  intro r
  classical
  let S : Set ℕ := {t : ℕ | 1 ≤ t ∧ t ^ k ≤ r}
  let f : Fin n × ℕ → FreeAbelianMonoid n := fun p => (p.2 ^ k) • ({p.1} : FreeAbelianMonoid n)

  -- Step 1: inclusion into an image
  have hsubset : Gpow n k ∩ Ball r (A n) ⊆ f '' ((Set.univ : Set (Fin n)) ×ˢ S) := by
    intro m hm
    rcases hm with ⟨hmG, hmB⟩
    rcases hmG with ⟨i, t, ht1, rfl⟩
    have hcard : (((t ^ k) • ({i} : FreeAbelianMonoid n)).card ≤ r) := by
      exact (Ball_A_iff_card_le (n := n) r ((t ^ k) • ({i} : FreeAbelianMonoid n))).1 hmB
    have htkr : t ^ k ≤ r := by
      simpa [Multiset.card_nsmul, Multiset.card_singleton, Nat.mul_one] using hcard
    refine ⟨(i, t), ?_, rfl⟩
    have : t ∈ S := by
      dsimp [S]
      exact ⟨ht1, htkr⟩
    simpa [Set.mem_prod, this]

  -- finiteness of S and of the product, to use `ncard` monotonicity
  have hk0 : k ≠ 0 := by
    have hkpos : 0 < k := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk
    exact Nat.ne_of_gt hkpos
  have hSsub : S ⊆ {t : ℕ | t ≤ r} := by
    intro t ht
    dsimp [S] at ht
    rcases ht with ⟨ht1, htkr⟩
    have ht_le : t ≤ t ^ k := le_self_pow ht1 hk0
    exact le_trans ht_le htkr
  have hSfinite : S.Finite := (Set.finite_le_nat r).subset hSsub
  have hUnivFinite : (Set.univ : Set (Fin n)).Finite := Set.finite_univ
  have hDomFinite : (((Set.univ : Set (Fin n)) ×ˢ S) : Set (Fin n × ℕ)).Finite :=
    hUnivFinite.prod hSfinite
  have hImgFinite : (f '' ((Set.univ : Set (Fin n)) ×ˢ S)).Finite := hDomFinite.image f

  -- Step 2: cardinality bounds
  have hle : (Gpow n k ∩ Ball r (A n)).ncard ≤ (f '' ((Set.univ : Set (Fin n)) ×ˢ S)).ncard := by
    exact Set.ncard_le_ncard hsubset hImgFinite
  have himage : (f '' ((Set.univ : Set (Fin n)) ×ˢ S)).ncard ≤ ((Set.univ : Set (Fin n)) ×ˢ S).ncard := by
    classical
    haveI : Finite (((Set.univ : Set (Fin n)) ×ˢ S) : Set (Fin n × ℕ)) := hDomFinite.to_subtype
    simpa using (Set.ncard_image_le (s := ((Set.univ : Set (Fin n)) ×ˢ S)) (f := f))
  have hprod : (((Set.univ : Set (Fin n)) ×ˢ S).ncard) = (Set.univ : Set (Fin n)).ncard * S.ncard := by
    simpa using (Set.ncard_prod (s := (Set.univ : Set (Fin n))) (t := S))
  have huniv : ((Set.univ : Set (Fin n)).ncard) = n := by
    simpa [Nat.card_fin] using (Set.ncard_univ (Fin n))

  have hnat : (Gpow n k ∩ Ball r (A n)).ncard ≤ n * S.ncard := by
    have : (Gpow n k ∩ Ball r (A n)).ncard ≤ ((Set.univ : Set (Fin n)) ×ˢ S).ncard :=
      le_trans hle himage
    simpa [hprod, huniv, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this

  -- Step 3: apply the 1D bound on S
  have hS : (S.ncard : ℝ) ≤ Real.rpow r ((1 : ℝ) / k) := by
    simpa [S] using (ncard_pow_le_rpow k r hk)

  -- cast to ℝ and finish
  have hnatR : ((Gpow n k ∩ Ball r (A n)).ncard : ℝ) ≤ (n * S.ncard : ℝ) := by
    exact_mod_cast hnat

  calc
    ((Gpow n k ∩ Ball r (A n)).ncard : ℝ) ≤ (n * S.ncard : ℝ) := hnatR
    _ = (n : ℝ) * (S.ncard : ℝ) := by
      norm_cast
    _ ≤ (n : ℝ) * Real.rpow r ((1 : ℝ) / k) := by
      have hn0 : 0 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      exact mul_le_mul_of_nonneg_left hS hn0


theorem theorem_3_polynomial_density (n k : ℕ) (hk : k ≥ 2) :
  ∃ (G : Set (FreeAbelianMonoid n)),
    (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ n * (Real.rpow r ((1 : ℝ) / k))) ∧
    (∀ (s : ℕ), (isWarring k s) → (∀ (r : ℕ), (Ball r (A n)) ⊆ (Ball (n * s) G))) := by
  classical
  refine ⟨Gpow n k, ?_, ?_⟩
  · intro r
    simpa using (Gpow_density n k hk r)
  · intro s hs
    intro r
    simpa using (Gpow_expansion n k s hk hs r)


