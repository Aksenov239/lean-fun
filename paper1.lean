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

end abelian

namespace free

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeMonoid (Fin n))) : Set (FreeMonoid (Fin n)) :=
  {m | ∃ l : List (FreeMonoid (Fin n)), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.prod = m}

def A (n : ℕ) : Set (FreeMonoid (Fin n)) :=
  { [i] | i : Fin n}

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

theorem theorem_5_polynomial_density
  (n : ℕ) (hn : n ≥ 2)
  (G : Set (FreeMonoid (Fin n)))
  (c : ℝ) (hc : c > 0)
  (p : ℝ) (hp : p ≥ 0)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c * Real.rpow l p )) :
    ∀ (s d : ℕ), (isGoodDLemma5 n c p d) → ¬ (Ball (d * s) (A n) ⊆ Ball s (G ∪ (A n))) :=
    sorry

end free

abbrev FreeAbelianMonoid (n : ℕ) := Multiset (Fin n)

def A (n : ℕ) : Set (FreeAbelianMonoid n) :=
  { {i} | i : Fin n}

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) : Set (FreeAbelianMonoid n) :=
  {m | ∃ l : List (FreeAbelianMonoid n),
    l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

def Gpow (n k : ℕ) : Set (FreeAbelianMonoid n) :=
  {m | ∃ (i : Fin n) (a : ℕ), 2 ≤ a ∧ m = Multiset.replicate (a ^ k) i}

def isWarring (k : ℕ) (n : ℕ) : Prop :=
  ∀ x : ℕ, ∃ l : List ℕ, l.length ≤ n ∧ (l.map (fun (y : ℕ) => y ^ k)).sum = x

theorem ncard_pow_set_le_rpow (k r : ℕ) (hk : 2 ≤ k) :
  (Set.ncard {a : ℕ | 2 ≤ a ∧ a ^ k ≤ r} : ℝ) ≤ Real.rpow (r : ℝ) ((1 : ℝ) / k) := by
  classical
  set S : Set ℕ := {a : ℕ | 2 ≤ a ∧ a ^ k ≤ r}
  set t : ℝ := Real.rpow (r : ℝ) ((1 : ℝ) / k)
  set m : ℕ := Nat.floor t
  have hk0 : k ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hk)
  have hr0 : 0 ≤ (r : ℝ) := by
    exact_mod_cast (Nat.zero_le r)
  have ht0 : 0 ≤ t := by
    simpa [t] using (Real.rpow_nonneg hr0 ((1 : ℝ) / k))
  have ht_pow : t ^ k = (r : ℝ) := by
    simpa [t, one_div] using (Real.rpow_inv_natCast_pow (x := (r : ℝ)) (n := k) hr0 hk0)
  have ha_le_t : ∀ {a : ℕ}, a ∈ S → (a : ℝ) ≤ t := by
    intro a ha
    have hpow : a ^ k ≤ r := ha.2
    have hpowR : (a : ℝ) ^ k ≤ (r : ℝ) := by
      exact_mod_cast hpow
    have hpowR' : (a : ℝ) ^ k ≤ t ^ k := by
      simpa [ht_pow] using hpowR
    have ha0 : 0 ≤ (a : ℝ) := by
      exact_mod_cast (Nat.zero_le a)
    have := (pow_le_pow_iff_left₀ ha0 ht0 hk0).1 hpowR'
    simpa using this
  have ha_le_m : ∀ {a : ℕ}, a ∈ S → a ≤ m := by
    intro a ha
    have : a ≤ Nat.floor t := Nat.le_floor (ha_le_t (a := a) ha)
    simpa [m] using this
  -- define the target set as range m
  set T : Set ℕ := (Finset.range m : Set ℕ)
  have hmaps : Set.MapsTo (fun a : ℕ => a - 1) S T := by
    intro a ha
    have ha2 : 2 ≤ a := ha.1
    have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_two ha2
    have hlt : a - 1 < a := by
      simpa using (tsub_lt_self ha0 (by decide : 0 < (1 : ℕ)))
    have ham : a ≤ m := ha_le_m (a := a) ha
    have : a - 1 < m := lt_of_lt_of_le hlt ham
    -- membership in range m
    have : a - 1 ∈ Finset.range m := by
      exact Finset.mem_range.2 this
    simpa [T] using this
  have hinj : Set.InjOn (fun a : ℕ => a - 1) S := by
    intro a ha b hb hab
    have ha1 : 1 ≤ a := le_trans (by decide : (1 : ℕ) ≤ 2) ha.1
    have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb.1
    exact (tsub_left_inj (c := 1) ha1 hb1).1 hab
  -- apply ncard_le_ncard_of_injOn
  have hcard : S.ncard ≤ T.ncard := by
    exact Set.ncard_le_ncard_of_injOn (f := fun a : ℕ => a - 1) hmaps hinj
  -- compute T.ncard
  have hT : T.ncard = m := by
    -- T is range m
    simpa [T] using (Set.ncard_coe_finset (Finset.range m))
  -- thus S.ncard ≤ m
  have hSm : S.ncard ≤ m := by
    simpa [hT] using hcard
  -- cast to reals and use floor_le
  have hSmR : (S.ncard : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hSm
  have hm_le_t : (m : ℝ) ≤ t := by
    -- use Nat.floor_le
    simpa [m] using (Nat.floor_le (R := ℝ) ht0)
  have : (S.ncard : ℝ) ≤ t := le_trans hSmR hm_le_t
  -- finish
  simpa [S, t] using this

theorem replicate_pow_mem_BallA_iff (n k r : ℕ) (i : Fin n) (a : ℕ) :
  Multiset.replicate (a ^ k) i ∈ Ball r (A n) ↔ a ^ k ≤ r := by
  constructor
  · intro hm
    rcases hm with ⟨l, hlr, hlA, hsum⟩
    -- lemma: singleton multisets have card 1, so the card of the list sum is the list length
    have hcard : ∀ l : List (FreeAbelianMonoid n),
        (∀ x, x ∈ l → x ∈ A n) → (l.sum).card = l.length := by
      classical
      intro l
      induction l with
      | nil =>
          intro h
          simp
      | cons x xs ih =>
          intro h
          have hxA : x ∈ A n := h x (by simp)
          have hxsA : ∀ y, y ∈ xs → y ∈ A n := by
            intro y hy
            exact h y (by simp [hy])
          rcases hxA with ⟨j, rfl⟩
          -- reduce to the inductive hypothesis on `xs`
          simp [List.sum_cons, Multiset.card_add, ih hxsA]
    have hsumcard : l.sum.card = a ^ k := by
      simpa using congrArg Multiset.card hsum
    have hlen : l.length = a ^ k := by
      have : l.sum.card = l.length := hcard l hlA
      exact this.symm.trans hsumcard
    simpa [hlen] using hlr
  · intro hk
    refine ⟨List.replicate (a ^ k) ({i} : Multiset (Fin n)), ?_, ?_, ?_⟩
    · simpa using hk
    · intro x hx
      -- every element of the replicate list is `{i}`
      rcases (List.mem_replicate.1 hx) with ⟨_, rfl⟩
      exact ⟨i, rfl⟩
    · simp [List.sum_replicate, Multiset.nsmul_singleton]


theorem Gpow_density (n k : ℕ) (hk : 2 ≤ k) :
  ∀ r : ℕ, (Gpow n k ∩ Ball r (A n)).ncard ≤ (n : ℝ) * Real.rpow (r : ℝ) ((1 : ℝ) / k) := by
  intro r
  classical
  let S : Set ℕ := {a : ℕ | 2 ≤ a ∧ a ^ k ≤ r}
  let f : Fin n × ℕ → FreeAbelianMonoid n := fun p => Multiset.replicate (p.2 ^ k) p.1
  have hrepr : Gpow n k ∩ Ball r (A n) = f '' ((Set.univ : Set (Fin n)) ×ˢ S) := by
    ext m
    constructor
    · intro hm
      rcases hm.1 with ⟨i, a, ha2, rfl⟩
      have har : a ^ k ≤ r := by
        exact (replicate_pow_mem_BallA_iff n k r i a).1 hm.2
      refine ⟨(i, a), ?_, by simp [f]⟩
      simp [S, ha2, har]
    · intro hm
      rcases hm with ⟨p, hp, rfl⟩
      have ha : 2 ≤ p.2 ∧ p.2 ^ k ≤ r := by
        simpa [S] using (show p.2 ∈ S from (by simpa using hp.2))
      refine ⟨?_, ?_⟩
      · refine ⟨p.1, p.2, ha.1, by simp [f]⟩
      · simpa [f] using (replicate_pow_mem_BallA_iff n k r p.1 p.2).2 ha.2
  have hk0 : k ≠ 0 := by
    have h02 : (0 : ℕ) < 2 := by decide
    exact Nat.ne_of_gt (lt_of_lt_of_le h02 hk)
  have hinj : Set.InjOn f ((Set.univ : Set (Fin n)) ×ˢ S) := by
    intro p hp q hq hpq
    have ha : 2 ≤ p.2 ∧ p.2 ^ k ≤ r := by
      simpa [S] using (show p.2 ∈ S from (by simpa using hp.2))
    have ha0 : p.2 ≠ 0 := by
      have h02 : (0 : ℕ) < 2 := by decide
      exact Nat.ne_of_gt (lt_of_lt_of_le h02 ha.1)
    have hpow_ne0 : p.2 ^ k ≠ 0 := pow_ne_zero k ha0
    have hcount : p.2 ^ k = q.2 ^ k := by
      have := congrArg Multiset.card hpq
      simpa [f] using this
    have hi : p.1 = q.1 := by
      have hpq' : Multiset.replicate (p.2 ^ k) p.1 = Multiset.replicate (p.2 ^ k) q.1 := by
        simpa [f, hcount] using hpq
      exact (Multiset.replicate_right_injective (n := p.2 ^ k) (α := Fin n) hpow_ne0) hpq'
    have haeq : p.2 = q.2 := (Nat.pow_left_injective hk0) hcount
    ext <;> simp [hi, haeq]
  have hncard_inter : (Gpow n k ∩ Ball r (A n)).ncard = (((Set.univ : Set (Fin n)) ×ˢ S).ncard) := by
    calc
      (Gpow n k ∩ Ball r (A n)).ncard = (f '' ((Set.univ : Set (Fin n)) ×ˢ S)).ncard := by
        simpa [hrepr]
      _ = (((Set.univ : Set (Fin n)) ×ˢ S).ncard) := by
        simpa using (Set.ncard_image_of_injOn (f := f) (s := ((Set.univ : Set (Fin n)) ×ˢ S)) hinj)
  have hncard_prod : (((Set.univ : Set (Fin n)) ×ˢ S).ncard : ℝ) = (n : ℝ) * (S.ncard : ℝ) := by
    have hprodNat : (((Set.univ : Set (Fin n)) ×ˢ S).ncard) = (Set.univ : Set (Fin n)).ncard * S.ncard := by
      simpa using (Set.ncard_prod (s := (Set.univ : Set (Fin n))) (t := S))
    have huniv : ((Set.univ : Set (Fin n)).ncard) = n := by
      simpa using (Set.ncard_univ (Fin n))
    -- cast hprodNat to ℝ and simplify
    have hprodReal : (((Set.univ : Set (Fin n)) ×ˢ S).ncard : ℝ) = ((Set.univ : Set (Fin n)).ncard : ℝ) * (S.ncard : ℝ) := by
      exact_mod_cast hprodNat
    -- now substitute huniv
    simpa [huniv] using hprodReal
  have hSbound : (S.ncard : ℝ) ≤ Real.rpow (r : ℝ) ((1 : ℝ) / k) := by
    simpa [S] using (ncard_pow_set_le_rpow k r hk)
  have : ((Gpow n k ∩ Ball r (A n)).ncard : ℝ) ≤ (n : ℝ) * Real.rpow (r : ℝ) ((1 : ℝ) / k) := by
    have hncard_inter' : ((Gpow n k ∩ Ball r (A n)).ncard : ℝ) = (((Set.univ : Set (Fin n)) ×ˢ S).ncard : ℝ) := by
      exact_mod_cast hncard_inter
    calc
      ((Gpow n k ∩ Ball r (A n)).ncard : ℝ)
          = (((Set.univ : Set (Fin n)) ×ˢ S).ncard : ℝ) := hncard_inter'
      _ = (n : ℝ) * (S.ncard : ℝ) := hncard_prod
      _ ≤ (n : ℝ) * Real.rpow (r : ℝ) ((1 : ℝ) / k) := by
            gcongr
  simpa using this


theorem waring_coord_decomp (n k g : ℕ) (hg : isWarring k g) (i : Fin n) (x : ℕ) :
  ∃ l : List (FreeAbelianMonoid n),
    l.length ≤ g ∧ (∀ m, m ∈ l → m ∈ (Gpow n k ∪ A n)) ∧ l.sum = Multiset.replicate x i := by
  classical
  cases k with
  | zero =>
      rcases hg x with ⟨t, htlen, htsum⟩
      let l : List (FreeAbelianMonoid n) :=
        t.map (fun y : ℕ => Multiset.replicate (y ^ 0) i)
      refine ⟨l, ?_⟩
      refine ⟨?_, ?_⟩
      · -- length bound
        simpa [l] using htlen
      · refine ⟨?_, ?_⟩
        · -- membership
          intro m hm
          have hm' : m ∈ t.map (fun y : ℕ => Multiset.replicate (y ^ 0) i) := by
            simpa [l] using hm
          rcases List.mem_map.1 hm' with ⟨y, hy, rfl⟩
          refine Or.inr ?_
          refine ⟨i, ?_⟩
          simp [pow_zero, Multiset.replicate_one]
        · -- sum
          let repHom : ℕ →+ Multiset (Fin n) := Multiset.replicateAddMonoidHom i
          let tPow : List ℕ := t.map (fun y : ℕ => y ^ 0)
          have htPowSum : tPow.sum = x := by
            simpa [tPow] using htsum
          have hlEq : l = tPow.map repHom := by
            simp [l, tPow, repHom, List.map_map, Multiset.replicateAddMonoidHom_apply]
          have hlSum : l.sum = Multiset.replicate tPow.sum i := by
            have h := (AddMonoidHom.map_list_sum repHom tPow).symm
            calc
              l.sum = (tPow.map repHom).sum := by
                simpa [hlEq]
              _ = repHom tPow.sum := by
                exact h
              _ = Multiset.replicate tPow.sum i := by
                simpa [repHom, Multiset.replicateAddMonoidHom_apply]
          rw [hlSum, htPowSum]
  | succ k =>
      rcases hg x with ⟨t, htlen, htsum⟩
      -- filter out zeros
      let t' : List ℕ := t.filter (fun y : ℕ => y ≠ 0)
      let l : List (FreeAbelianMonoid n) :=
        t'.map (fun y : ℕ => Multiset.replicate (y ^ Nat.succ k) i)
      refine ⟨l, ?_⟩
      refine ⟨?_, ?_⟩
      · -- length bound
        have hlen_filter : ∀ s : List ℕ, (s.filter (fun y : ℕ => y ≠ 0)).length ≤ s.length := by
          intro s
          induction s with
          | nil =>
              simp
          | cons a s ih =>
              by_cases ha : a = 0
              · subst ha
                have : (s.filter (fun y : ℕ => y ≠ 0)).length ≤ Nat.succ s.length :=
                  le_trans ih (Nat.le_succ _)
                simpa using this
              · have : Nat.succ (s.filter (fun y : ℕ => y ≠ 0)).length ≤ Nat.succ s.length :=
                  Nat.succ_le_succ ih
                simpa [List.filter, ha] using this
        have ht'len : t'.length ≤ g := by
          have : t'.length ≤ t.length := by
            simpa [t'] using hlen_filter t
          exact le_trans this htlen
        simpa [l] using ht'len
      · refine ⟨?_, ?_⟩
        · -- membership
          intro m hm
          have hm' : m ∈ t'.map (fun y : ℕ => Multiset.replicate (y ^ Nat.succ k) i) := by
            simpa [l] using hm
          rcases List.mem_map.1 hm' with ⟨y, hy, rfl⟩
          have hy0 : y ≠ 0 := by
            have hy' : y ∈ t.filter (fun y : ℕ => y ≠ 0) := by
              simpa [t'] using hy
            simpa using (List.of_mem_filter hy')
          by_cases hy1 : y = 1
          · subst hy1
            refine Or.inr ?_
            refine ⟨i, ?_⟩
            simp [Multiset.replicate_one]
          · have hy2 : 2 ≤ y := (Nat.two_le_iff y).2 ⟨hy0, hy1⟩
            refine Or.inl ?_
            exact ⟨i, y, ⟨hy2, rfl⟩⟩
        · -- sum
          let f : ℕ → ℕ := fun y : ℕ => y ^ Nat.succ k
          have hzero : ∀ s : List ℕ, ((s.filter (fun y : ℕ => y = 0)).map f).sum = 0 := by
            intro s
            induction s with
            | nil =>
                simp [f]
            | cons a s ih =>
                by_cases ha : a = 0
                · subst ha
                  simp [f, ih]
                · simp [List.filter, ha, ih, f]
          have hfilterSum : ((t.filter (fun y : ℕ => y ≠ 0)).map f).sum = (t.map f).sum := by
            have h :=
              List.sum_map_filter_add_sum_map_filter_not (l := t) (p := fun y : ℕ => y = 0) (f := f)
            have hz : ((t.filter (fun y : ℕ => y = 0)).map f).sum = 0 := hzero t
            have h' : ((t.filter (fun y : ℕ => ¬ y = 0)).map f).sum = (t.map f).sum := by
              simpa [hz] using h
            simpa using h'
          have htPowSum : (t'.map f).sum = x := by
            have : ((t.filter (fun y : ℕ => y ≠ 0)).map f).sum = x := hfilterSum.trans htsum
            simpa [t', f] using this
          let repHom : ℕ →+ Multiset (Fin n) := Multiset.replicateAddMonoidHom i
          let tPow : List ℕ := t'.map f
          have hlEq : l = tPow.map repHom := by
            simp [l, tPow, repHom, f, List.map_map, Multiset.replicateAddMonoidHom_apply]
          have hlSum : l.sum = Multiset.replicate tPow.sum i := by
            have h := (AddMonoidHom.map_list_sum repHom tPow).symm
            calc
              l.sum = (tPow.map repHom).sum := by
                simpa [hlEq]
              _ = repHom tPow.sum := by
                exact h
              _ = Multiset.replicate tPow.sum i := by
                simpa [repHom, Multiset.replicateAddMonoidHom_apply]
          have : tPow.sum = x := by
            simpa [tPow] using htPowSum
          rw [hlSum, this]


theorem mem_Ball_Gpow_union_of_isWarring (n k g : ℕ) (hg : isWarring k g) :
  ∀ m : FreeAbelianMonoid n, m ∈ Ball (n * g) (Gpow n k ∪ A n) := by
  intro m
  classical
  -- Let `S` be the finite set of generators appearing in `m`.
  let S : Finset (Fin n) := m.toFinset

  -- First build a list whose sum is the `Finset`-sum of the coordinate contributions.
  have hdecomp :
      ∃ l : List (FreeAbelianMonoid n),
        l.length ≤ S.card * g ∧
          (∀ x, x ∈ l → x ∈ (Gpow n k ∪ A n)) ∧
          l.sum = ∑ i ∈ S, Multiset.replicate (m.count i) i := by
    classical
    -- Induction over the finset `S`.
    refine Finset.induction_on S ?base ?step
    · -- base case
      refine ⟨[], ?_, ?_, ?_⟩
      · simp
      · intro x hx
        simpa using hx
      · simp
    · intro a s ha hs
      rcases hs with ⟨l, hl_len, hl_mem, hl_sum⟩

      -- Decompose the `a`-coordinate using `waring_coord_decomp`.
      let la : List (FreeAbelianMonoid n) :=
        Classical.choose (waring_coord_decomp n k g hg a (m.count a))
      have hla :
          la.length ≤ g ∧
            (∀ x, x ∈ la → x ∈ (Gpow n k ∪ A n)) ∧
            la.sum = Multiset.replicate (m.count a) a :=
        Classical.choose_spec (waring_coord_decomp n k g hg a (m.count a))

      refine ⟨la ++ l, ?_, ?_, ?_⟩
      · -- length bound
        have hlen : (la ++ l).length ≤ g + s.card * g := by
          simpa [List.length_append] using Nat.add_le_add hla.1 hl_len
        have hcardmul : g + s.card * g = (insert a s).card * g := by
          calc
            g + s.card * g = s.card * g + g := by simp [Nat.add_comm]
            _ = (s.card + 1) * g := by
              simpa [Nat.succ_eq_add_one] using (Nat.succ_mul s.card g).symm
            _ = (insert a s).card * g := by
              simp [Finset.card_insert_of_not_mem ha]
        exact le_trans hlen (le_of_eq hcardmul)
      · -- membership
        intro x hx
        have hx' : x ∈ la ∨ x ∈ l := by
          simpa [List.mem_append] using hx
        cases hx' with
        | inl hxla =>
            exact hla.2.1 x hxla
        | inr hxl =>
            exact hl_mem x hxl
      · -- sum computation
        simp [List.sum_append, hla.2.2, hl_sum, Finset.sum_insert, ha]

  rcases hdecomp with ⟨l, hl_len, hl_mem, hl_sum⟩

  -- Convert the `S.card * g` bound into `n * g`.
  have hcard : S.card ≤ n := by
    simpa using (card_finset_fin_le S)

  refine ⟨l, ?_, ?_, ?_⟩
  · exact le_trans hl_len (Nat.mul_le_mul_right g hcard)
  · exact hl_mem
  ·
    have hsum_finset : (∑ i ∈ S, Multiset.replicate (m.count i) i) = m := by
      -- `Multiset.toFinset_sum_count_nsmul_eq` plus `Multiset.nsmul_singleton`.
      simpa [S, Multiset.nsmul_singleton] using (Multiset.toFinset_sum_count_nsmul_eq m)
    exact hl_sum.trans hsum_finset

theorem theorem_3_polynomial_density (n k : ℕ) (hk : k ≥ 2) :
  ∃ (G : Set (FreeAbelianMonoid n)),
    (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ n * (Real.rpow r ((1 : ℝ) / k))) ∧
    (∀ (g : ℕ), (isWarring k g) → (∀ (r : ℕ), (Ball r (A n)) ⊆ (Ball (n * g) (G ∪ (A n))))) := by
  refine ⟨Gpow n k, ?_, ?_⟩
  · intro r
    simpa using (Gpow_density n k hk r)
  · intro g hg
    intro r
    intro m hm
    exact mem_Ball_Gpow_union_of_isWarring n k g hg m


