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

/-- The macro set
`M = { a_i^(b^j) : i = 1..n, j ≥ 1 }`,
modeled as multisets with `b^j` copies of generator `i`. -/
def MacroSet (n b : ℕ) : Set (FreeAbelianMonoid n) :=
  { m | ∃ i : Fin n, ∃ j : ℕ, 1 ≤ j ∧ m = Multiset.replicate (b ^ j) i }

theorem theorem_2_quasi_exponential_expansion
  (n : ℕ)
  (G : Set (FreeAbelianMonoid n))
  (c q : ℝ) :
  (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) →
    (∃ (K : ℕ), ∀ (s : ℕ), (s ≥ 2) → ((K ≥ 0) ∧
      let r := 1 + Int.toNat <| Int.floor <| Real.exp (K * s * (Real.log s))
      ¬ (Ball r (A n) ⊆ Ball s (G ∪ (A n))))) :=
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
  {m | ∃ l : List (FreeAbelianMonoid n), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

theorem Ball_mono_radius (n R S : ℕ) (X : Set (FreeAbelianMonoid n)) : R ≤ S → Ball R X ⊆ Ball S X := by
  intro hRS
  intro m hm
  rcases hm with ⟨l, hlR, hX, hsum⟩
  refine ⟨l, le_trans hlR hRS, hX, hsum⟩


def HardElement (n b k : ℕ) : FreeAbelianMonoid n :=
  (Finset.univ : Finset (Fin n)).sum (fun i => Multiset.replicate (b ^ k - 1) i)

def MacroSet (n b : ℕ) : Set (FreeAbelianMonoid n) :=
  { m | ∃ i : Fin n, ∃ j : ℕ, 1 ≤ j ∧ m = Multiset.replicate (b ^ j) i }

def digitBallList (n b : ℕ) (i : Fin n) (x : ℕ) : List (FreeAbelianMonoid n) :=
  ((Nat.digits b x).mapIdx (fun j d => List.replicate d (Multiset.replicate (b ^ j) i))).flatten

theorem digitBallList_length (n b : ℕ) (i : Fin n) (x : ℕ) : (digitBallList n b i x).length = (Nat.digits b x).sum := by
  classical
  unfold digitBallList
  simp [List.length_flatten, List.mapIdx_eq_ofFn, List.map_ofFn]
  -- The function used in `ofFn` is just the digit itself, since
  -- `length (replicate d _) = d`.
  have hfun :
      (List.length ∘
          (fun i_1 : Fin (b.digits x).length =>
            List.replicate (b.digits x)[(i_1 : Nat)] (Multiset.replicate (b ^ (i_1 : Nat)) i))) =
        (fun i_1 : Fin (b.digits x).length => (b.digits x)[(i_1 : Nat)]) := by
    funext i_1
    simp [Function.comp]
  -- Now `ofFn` reconstructs the list from its entries.
  simpa [hfun] using congrArg List.sum (List.ofFn_getElem (l := b.digits x))


theorem digitBallList_mem (n b : ℕ) (hb : 2 ≤ b) (i : Fin n) (x : ℕ) :
  ∀ m, m ∈ digitBallList n b i x → m ∈ MacroSet n b ∪ A n := by
  intro m hm
  unfold digitBallList at hm
  rcases List.mem_flatten.1 hm with ⟨l, hl, hml⟩
  have hl' : l ∈ List.ofFn (fun j : Fin (Nat.digits b x).length =>
      List.replicate ((Nat.digits b x).get j) (Multiset.replicate (b ^ (j : ℕ)) i)) := by
    simpa [List.mapIdx_eq_ofFn] using hl
  have hlrange : l ∈ Set.range (fun j : Fin (Nat.digits b x).length =>
      List.replicate ((Nat.digits b x).get j) (Multiset.replicate (b ^ (j : ℕ)) i)) :=
    (List.mem_ofFn' _ l).1 hl'
  rcases hlrange with ⟨j, rfl⟩
  have hmEq : m = Multiset.replicate (b ^ (j : ℕ)) i := by
    rcases (List.mem_replicate.1 hml) with ⟨-, rfl⟩
    rfl
  subst hmEq
  cases (j : ℕ) with
  | zero =>
      right
      refine ⟨i, ?_⟩
      -- goal: {i} = Multiset.replicate 1 i
      simp [Multiset.replicate_one, A]
  | succ j' =>
      left
      refine ⟨i, Nat.succ j', ?_, rfl⟩
      exact Nat.succ_le_succ (Nat.zero_le j')


theorem digitBallList_sum (n b : ℕ) (hb : 2 ≤ b) (i : Fin n) (x : ℕ) :
  (digitBallList n b i x).sum = Multiset.replicate x i := by
  classical
  -- A lemma to commute `List.map` and `List.mapIdx`
  have map_mapIdx {α β γ : Type} (g : β → γ) (f : ℕ → α → β) (l : List α) :
      List.map g (List.mapIdx f l) = List.mapIdx (fun i a => g (f i a)) l := by
    simpa [List.mapIdx_eq_ofFn] using
      (List.ofFn_comp' (f := fun i : Fin l.length => f (i : ℕ) (l.get i)) g).symm

  unfold digitBallList
  -- Replace `digits` by a name
  set ds : List ℕ := Nat.digits b x
  -- Turn the `flatten` sum into a sum of sums
  simp [ds, List.sum_flatten]
  -- Push `List.sum` inside `mapIdx`
  rw [map_mapIdx (g := List.sum)
        (f := fun j d => List.replicate d (Multiset.replicate (b ^ j) i)) (l := ds)]
  -- Evaluate each digit-position block sum
  simp [List.sum_replicate, Multiset.nsmul_replicate]

  -- Combine the replicated multisets using the additive hom `replicateAddMonoidHom`
  set cs : List ℕ := List.mapIdx (fun j d => d * b ^ j) ds
  let φ : ℕ →+ Multiset (Fin n) := Multiset.replicateAddMonoidHom i

  have hlist : List.map φ cs = List.mapIdx (fun j d => Multiset.replicate (d * b ^ j) i) ds := by
    simpa [cs, φ, Multiset.replicateAddMonoidHom_apply] using
      (map_mapIdx (g := φ) (f := fun j d => d * b ^ j) (l := ds))

  -- Rewrite the list as a map of `φ`, then pull `φ` out of the sum.
  rw [hlist.symm]
  have hsum : (List.map φ cs).sum = φ cs.sum := by
    simpa using (φ.map_list_sum cs).symm
  rw [hsum]

  -- Identify the natural number `cs.sum` with `x` via digit expansion.
  have hcs_sum : cs.sum = x := by
    have h1 : Nat.ofDigits b ds = cs.sum := by
      simpa [cs] using (Nat.ofDigits_eq_sum_mapIdx b ds)
    have h2 : Nat.ofDigits b ds = x := by
      simpa [ds] using (Nat.ofDigits_digits b x)
    -- combine
    calc
      cs.sum = Nat.ofDigits b ds := by simpa using h1.symm
      _ = x := h2

  -- Finish.
  simpa [φ, Multiset.replicateAddMonoidHom_apply, hcs_sum]


theorem digits_sum_le_log_bound (b x : ℕ) (hb : 2 ≤ b) : (Nat.digits b x).sum ≤ (b - 1) * (Nat.log b x + 1) := by
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb
  classical
  by_cases hx : x = 0
  · subst hx
    simp [Nat.log_zero_right]
  ·
    have hle : ∀ d ∈ Nat.digits b x, d ≤ b - 1 := by
      intro d hd
      have hdlt : d < b := Nat.digits_lt_base hb1 hd
      have hb_succ : b = Nat.succ (b - 1) := by
        have hbpos : 1 ≤ b := le_of_lt hb1
        have : b = (b - 1) + 1 := by
          simpa using (Nat.sub_add_cancel hbpos).symm
        simpa [Nat.succ_eq_add_one] using this
      have : d < Nat.succ (b - 1) := lt_of_lt_of_eq hdlt hb_succ
      exact Nat.lt_succ_iff.mp this
    have hsum : (Nat.digits b x).sum ≤ (Nat.digits b x).length • (b - 1) := by
      exact List.sum_le_card_nsmul (l := Nat.digits b x) (n := b - 1) hle
    have hlen : (Nat.digits b x).length = Nat.log b x + 1 := by
      simpa using (Nat.digits_len b x hb1 hx)
    have hsum' : (Nat.digits b x).sum ≤ (Nat.digits b x).length * (b - 1) := by
      simpa [Nat.nsmul_eq_mul] using hsum
    calc
      (Nat.digits b x).sum ≤ (Nat.digits b x).length * (b - 1) := hsum'
      _ = (Nat.log b x + 1) * (b - 1) := by simpa [hlen]
      _ = (b - 1) * (Nat.log b x + 1) := by ac_rfl

theorem mem_Ball_A_of_card_le (n R : ℕ) (m : FreeAbelianMonoid n) : m.card ≤ R → m ∈ Ball R (A n) := by
  intro hm
  classical
  let l0 : List (Fin n) := m.toList
  let l : List (FreeAbelianMonoid n) := l0.map (fun i => ({i} : Multiset (Fin n)))
  refine ⟨l, ?_, ?_, ?_⟩
  · -- length bound
    -- l.length = m.card
    simpa [l, l0] using hm
  · -- members in A
    intro x hx
    rcases List.mem_map.1 hx with ⟨i, hi, rfl⟩
    refine ⟨i, rfl⟩
  · -- sum
    -- prove by induction on l0
    -- first show sum of singleton multisets equals multiset of list
    have hsum : (l0.map (fun i => ({i} : Multiset (Fin n)))).sum = (l0 : Multiset (Fin n)) := by
      induction l0 with
      | nil =>
          simp
      | cons a t ih =>
          simp [ih]
    -- now use coe_toList
    simpa [l, l0, hsum]

theorem mem_Ball_A_iff_card_le (n R : ℕ) (m : FreeAbelianMonoid n) : m ∈ Ball R (A n) ↔ m.card ≤ R := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩
    have hcard_sum : ∀ l : List (FreeAbelianMonoid n),
        (∀ x, x ∈ l → x ∈ A n) → (l.sum).card = l.length := by
      intro l
      induction l with
      | nil =>
          intro hl
          simp
      | cons a l ih =>
          intro hl
          have ha : a ∈ A n := hl a (by simp)
          have hl' : ∀ x, x ∈ l → x ∈ A n := by
            intro x hx
            exact hl x (by simp [hx])
          rcases ha with ⟨i, rfl⟩
          -- reduce to card_add + IH
          simpa [Multiset.card_add, ih hl']
    have hcard : m.card = l.length := by
      simpa [hl_sum] using (hcard_sum l hl_mem)
    simpa [hcard] using hl_len
  · intro hmcard
    exact mem_Ball_A_of_card_le n R m hmcard


theorem hardElement_mem_Ball_A (n b k : ℕ) : HardElement n b k ∈ Ball (n * b ^ k) (A n) := by
  classical
  -- reduce membership in Ball to a cardinality inequality
  rw [mem_Ball_A_iff_card_le n (n * b ^ k) (HardElement n b k)]
  -- compute the cardinality of `HardElement`
  have hcard : (HardElement n b k).card = n * (b ^ k - 1) := by
    classical
    -- use `Multiset.card_sum` and `Multiset.card_replicate`
    simp [HardElement, Multiset.card_sum]
  -- use the computed cardinality
  -- `b^k - 1 ≤ b^k`
  have hle : n * (b ^ k - 1) ≤ n * b ^ k := by
    exact Nat.mul_le_mul_left n (Nat.sub_le (b ^ k) 1)
  -- finish
  simpa [hcard] using hle

theorem macro_mem_Ball_A_iff (n b x : ℕ) (i : Fin n) (j : ℕ) (hj : 1 ≤ j) : Multiset.replicate (b ^ j) i ∈ Ball x (A n) ↔ b ^ j ≤ x := by
  -- Reduce to a statement about the card of the multiset.
  simpa [Multiset.card_replicate] using
    (mem_Ball_A_iff_card_le n x (Multiset.replicate (b ^ j) i))


theorem mem_MacroSet_union_A_exists_replicate_pow (n b : ℕ) (m : FreeAbelianMonoid n) : m ∈ MacroSet n b ∪ A n → ∃ (i : Fin n) (j : ℕ), m = Multiset.replicate (b ^ j) i := by
  intro hm
  rcases hm with hm | hm
  · rcases hm with ⟨i, j, hj, rfl⟩
    exact ⟨i, j, rfl⟩
  · rcases hm with ⟨i, rfl⟩
    refine ⟨i, 0, ?_⟩
    simp [Multiset.replicate_one]

theorem ncard_MacroSet_inter_Ball (n b x : ℕ) (hb : 2 ≤ b) : (MacroSet n b ∩ Ball x (A n)).ncard = n * Nat.log b x := by
  classical
  by_cases hx : x = 0
  · subst hx
    have hempty : (MacroSet n b ∩ Ball 0 (A n)) = (∅ : Set (FreeAbelianMonoid n)) := by
      ext m
      constructor
      · intro hm
        rcases hm with ⟨hmMacro, hmBall⟩
        rcases hmMacro with ⟨i, j, hj, rfl⟩
        have hcard : (Multiset.replicate (b ^ j) i).card ≤ 0 :=
          (mem_Ball_A_iff_card_le n 0 (Multiset.replicate (b ^ j) i)).1 hmBall
        have hbj : b ^ j ≤ 0 := by
          simpa [Multiset.card_replicate] using hcard
        have hb0 : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
        have hne : b ^ j ≠ 0 := Nat.ne_of_gt (pow_pos hb0 j)
        exact (hne (Nat.eq_zero_of_le_zero hbj)).elim
      · intro hm
        simpa using hm
    simp [hempty, Nat.log_zero_right]
  ·
    have hb1 : 1 < b := lt_of_lt_of_le Nat.one_lt_two hb
    let L : ℕ := Nat.log b x
    let f : (Fin n × Fin L) → FreeAbelianMonoid n := fun p =>
      Multiset.replicate (b ^ (p.2.1 + 1)) p.1
    have hf_inj : Function.Injective f := by
      intro p q hpq
      have hcard := congrArg Multiset.card hpq
      have hpow : b ^ (p.2.1 + 1) = b ^ (q.2.1 + 1) := by
        simpa [f, Multiset.card_replicate] using hcard
      have hexp : p.2.1 + 1 = q.2.1 + 1 := (Nat.pow_right_injective hb) hpow
      have hexp' : p.2.1 = q.2.1 := Nat.add_right_cancel hexp
      have hk : p.2 = q.2 := by
        apply Fin.ext
        exact hexp'
      have hb0 : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
      have hne : b ^ (p.2.1 + 1) ≠ 0 := Nat.ne_of_gt (pow_pos hb0 (p.2.1 + 1))
      have hpq' : Multiset.replicate (b ^ (p.2.1 + 1)) p.1 =
          Multiset.replicate (b ^ (p.2.1 + 1)) q.1 := by
        have hpq_unfold : Multiset.replicate (b ^ (p.2.1 + 1)) p.1 =
            Multiset.replicate (b ^ (q.2.1 + 1)) q.1 := by
          simpa [f] using hpq
        simpa [hexp.symm] using hpq_unfold
      have hi : p.1 = q.1 := by
        exact (Multiset.replicate_right_injective (n := b ^ (p.2.1 + 1)) hne) hpq'
      exact Prod.ext hi hk

    have hEq : MacroSet n b ∩ Ball x (A n) = f '' (Set.univ : Set (Fin n × Fin L)) := by
      ext m
      constructor
      · intro hm
        rcases hm with ⟨hmMacro, hmBall⟩
        rcases hmMacro with ⟨i, j, hj, rfl⟩
        have hbj : b ^ j ≤ x := (macro_mem_Ball_A_iff n b x i j hj).1 hmBall
        have hjle : j ≤ Nat.log b x := (Nat.pow_le_iff_le_log hb1 hx).1 hbj
        have hk_lt : j - 1 < L := by
          have hj0 : 0 < j := lt_of_lt_of_le Nat.zero_lt_one hj
          have hsub : j - 1 < j := tsub_lt_self hj0 Nat.zero_lt_one
          exact lt_of_lt_of_le hsub (by simpa [L] using hjle)
        let k : Fin L := ⟨j - 1, hk_lt⟩
        refine ⟨(i, k), by trivial, ?_⟩
        simp [f, k, L, tsub_add_cancel_of_le hj]
      · intro hm
        rcases hm with ⟨p, -, rfl⟩
        rcases p with ⟨i, k⟩
        refine ⟨?_, ?_⟩
        · refine ⟨i, k.1 + 1, ?_, by simp [f]⟩
          exact Nat.succ_le_succ (Nat.zero_le k.1)
        ·
          have hj : 1 ≤ k.1 + 1 := Nat.succ_le_succ (Nat.zero_le k.1)
          have hjle : k.1 + 1 ≤ Nat.log b x := by
            have : k.1 + 1 ≤ L := Nat.succ_le_of_lt k.2
            simpa [L] using this
          have hpowle : b ^ (k.1 + 1) ≤ x :=
            Nat.pow_le_of_le_log (b := b) (x := k.1 + 1) (y := x) hx hjle
          exact (macro_mem_Ball_A_iff n b x i (k.1 + 1) hj).2 hpowle

    calc
      (MacroSet n b ∩ Ball x (A n)).ncard
          = (f '' (Set.univ : Set (Fin n × Fin L))).ncard := by
              simpa [hEq]
      _ = (Set.univ : Set (Fin n × Fin L)).ncard := by
              simpa using
                (Set.ncard_image_of_injective (s := (Set.univ : Set (Fin n × Fin L))) hf_inj)
      _ = Nat.card (Fin n × Fin L) := by
              simpa using (Set.ncard_univ (Fin n × Fin L))
      _ = Nat.card (Fin n) * Nat.card (Fin L) := by
              simpa using (Nat.card_prod (Fin n) (Fin L))
      _ = n * Nat.log b x := by
              simp [L, Nat.card_fin]


theorem macro_density_bounds (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b) :
  let M := MacroSet n b
  ∃ (d1 d2 : ℝ), 0 < d1 ∧ 0 < d2 ∧
    ∀ x : ℕ, x ≥ b →
      d1 * Real.log x ≤ (M ∩ Ball x (A n)).ncard ∧
      (M ∩ Ball x (A n)).ncard ≤ d2 * Real.log x := by
  classical
  dsimp
  -- choose explicit constants
  let d2 : ℝ := (n : ℝ) / Real.log b
  let d1 : ℝ := (n : ℝ) / (2 * Real.log b)
  refine ⟨d1, d2, ?_, ?_, ?_⟩
  · -- d1 > 0
    have hb1nat : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb
    have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1nat
    have hlogb : 0 < Real.log b := by simpa using Real.log_pos hb1
    have hn0nat : 0 < n := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn0nat
    have hden : 0 < (2 * Real.log b) := by nlinarith [hlogb]
    simpa [d1] using div_pos hn0 hden
  · -- d2 > 0
    have hb1nat : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb
    have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1nat
    have hlogb : 0 < Real.log b := by simpa using Real.log_pos hb1
    have hn0nat : 0 < n := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn0nat
    simpa [d2] using div_pos hn0 hlogb
  · intro x hx
    have hb1nat : 1 < b := lt_of_lt_of_le (by decide : 1 < 2) hb
    have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1nat
    have hlogb : 0 < Real.log b := by simpa using Real.log_pos hb1
    have hcard : (MacroSet n b ∩ Ball x (A n)).ncard = n * Nat.log b x :=
      ncard_MacroSet_inter_Ball n b x hb
    -- show `Nat.log b x ≥ 1` from `b ≤ x`
    have hlog_ge_one : (1 : ℕ) ≤ Nat.log b x := by
      have hbpow : b ^ (1 : ℕ) ≤ x := by simpa using hx
      simpa using Nat.le_log_of_pow_le hb1nat hbpow
    have hlog_ge_oneR : (1 : ℝ) ≤ (Nat.log b x : ℝ) := by exact_mod_cast hlog_ge_one

    -- inequalities comparing `Nat.log` and `Real.logb`
    have hnatlog_le_logb : (Nat.log b x : ℝ) ≤ Real.logb b x := Real.natLog_le_logb x b

    have hfloor : (⌊Real.logb b x⌋₊) = Nat.log b x := by
      simpa using (Real.natFloor_logb_natCast b x)
    have hlogb_lt : Real.logb b x < (Nat.log b x : ℝ) + 1 := by
      have : Real.logb b x < (⌊Real.logb b x⌋₊ : ℝ) + 1 := by
        simpa using (Nat.lt_floor_add_one (Real.logb b x))
      simpa [hfloor] using this
    have hlogb_le : Real.logb b x ≤ (Nat.log b x : ℝ) + 1 := le_of_lt hlogb_lt
    have hlogb_le_two_mul : Real.logb b x ≤ 2 * (Nat.log b x : ℝ) := by
      have h2 : (Nat.log b x : ℝ) + 1 ≤ 2 * (Nat.log b x : ℝ) := by
        nlinarith [hlog_ge_oneR]
      exact le_trans hlogb_le h2

    -- upper bound
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hupper_mul : (n : ℝ) * (Nat.log b x : ℝ) ≤ (n : ℝ) * Real.logb b x :=
      mul_le_mul_of_nonneg_left hnatlog_le_logb hnnonneg
    have hupper : (n : ℝ) * (Nat.log b x : ℝ) ≤ d2 * Real.log x := by
      have : (n : ℝ) * Real.logb b x = d2 * Real.log x := by
        simp [d2, Real.logb, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      simpa [this] using hupper_mul

    -- lower bound
    have hlog_div_two : Real.logb b x / 2 ≤ (Nat.log b x : ℝ) := by
      nlinarith [hlogb_le_two_mul]
    have hlog_le_natlog : Real.log x / (2 * Real.log b) ≤ (Nat.log b x : ℝ) := by
      have : Real.log x / (2 * Real.log b) = Real.logb b x / 2 := by
        calc
          Real.log x / (2 * Real.log b) = Real.log x / Real.log b / 2 := by
            simpa using
              (div_mul_eq_div_div_swap (a := Real.log x) (b := (2 : ℝ)) (c := Real.log b))
          _ = Real.logb b x / 2 := by
            -- `Real.log_div_log` rewrites `log x / log b` to `logb b x`
            simp [Real.log_div_log]
      simpa [this] using hlog_div_two

    have hlower_mul : (n : ℝ) * (Real.log x / (2 * Real.log b)) ≤ (n : ℝ) * (Nat.log b x : ℝ) :=
      mul_le_mul_of_nonneg_left hlog_le_natlog hnnonneg
    have hlower : d1 * Real.log x ≤ (n : ℝ) * (Nat.log b x : ℝ) := by
      have : d1 * Real.log x = (n : ℝ) * (Real.log x / (2 * Real.log b)) := by
        simp [d1, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      -- rewrite and close
      simpa [this] using hlower_mul

    constructor
    · -- lower bound, convert back to `ncard`
      simpa [hcard, Nat.cast_mul] using hlower
    · -- upper bound
      simpa [hcard, Nat.cast_mul] using hupper

theorem reduce_exponent_list (b k : ℕ) (hb : 2 ≤ b) (e : List ℕ) :
  (e.map (fun j => b ^ j)).sum = b ^ (k + 1) - 1 →
  ∃ e2 : List ℕ,
    (e2.map (fun j => b ^ j)).sum = b ^ k - 1 ∧
    e2.length + (b - 1) ≤ e.length := by
  intro hsum
  classical

  -- Split `e` into the zeros and the nonzeros.
  let e0 : List ℕ := e.filter (fun j => j = 0)
  let z : ℕ := e0.length
  let e1 : List ℕ := e.filter (fun j => j ≠ 0)

  have hsum_split :
      (e0.map (fun j => b ^ j)).sum + (e1.map (fun j => b ^ j)).sum =
        (e.map (fun j => b ^ j)).sum := by
    simpa [e0, e1, add_comm, add_left_comm, add_assoc] using
      (List.sum_map_filter_add_sum_map_filter_not (p := fun j : ℕ => j = 0)
        (f := fun j : ℕ => b ^ j) (l := e))

  -- The `e0` part is just `z`, since all exponents are `0`.
  have hsum0 : (e0.map (fun j => b ^ j)).sum = z := by
    have hconst : ∀ x ∈ e0.map (fun j => b ^ j), x = (1 : ℕ) := by
      intro x hx
      rcases List.mem_map.1 hx with ⟨j, hj, rfl⟩
      have hj0 : j = 0 := by
        have : decide (j = 0) = true := by
          simpa [e0] using (List.mem_filter.1 hj).2
        exact (Bool.decide_iff (j = 0)).1 this
      simpa [hj0]
    simpa [z] using
      (List.sum_eq_card_nsmul (l := e0.map (fun j => b ^ j)) (m := (1 : ℕ)) hconst)

  -- Define the shifted sum coming from the nonzero exponents.
  let T : ℕ := (e1.map (fun j => b ^ (j - 1))).sum

  have hsum1 : (e1.map (fun j => b ^ j)).sum = b * T := by
    have hmap : e1.map (fun j => b ^ j) = e1.map (fun j => b * b ^ (j - 1)) := by
      refine List.map_congr_left ?_
      intro j hj
      have hj0 : j ≠ 0 := by
        have : decide (j ≠ 0) = true := by
          simpa [e1] using (List.mem_filter.1 hj).2
        exact (Bool.decide_iff (j ≠ 0)).1 this
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hj' : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.succ_le_iff.1 hjpos)
      calc
        b ^ j = b ^ (j - 1 + 1) := by simpa [hj']
        _ = b ^ (j - 1) * b := by simpa [pow_succ]
        _ = b * b ^ (j - 1) := by ac_rfl
    calc
      (e1.map (fun j => b ^ j)).sum = (e1.map (fun j => b * b ^ (j - 1))).sum := by
        simpa [hmap]
      _ = b * (e1.map (fun j => b ^ (j - 1))).sum := by
        simpa using
          (List.sum_map_mul_left (l := e1) (f := fun j : ℕ => b ^ (j - 1)) (r := b))
      _ = b * T := by rfl

  -- Combine everything into a single equation.
  have hEq : z + b * T = b ^ (k + 1) - 1 := by
    have hEq0 : (e0.map (fun j => b ^ j)).sum + (e1.map (fun j => b ^ j)).sum = b ^ (k + 1) - 1 :=
      hsum_split.trans hsum
    simpa [hsum0, hsum1, add_assoc, add_comm, add_left_comm] using hEq0

  have hb1 : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  have hbpos : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
  have hbne0 : b ≠ 0 := Nat.ne_of_gt hbpos
  have hbpow1 : 1 ≤ b ^ (k + 1) := one_le_pow₀ hb1
  have hbpowk : 1 ≤ b ^ k := one_le_pow₀ hb1
  have hbsub : b - 1 < b := tsub_lt_self hbpos (by decide : (0 : ℕ) < 1)

  -- Show `z % b = b - 1` using modular arithmetic.
  have hmulMod : b * T ≡ 0 [MOD b] := (Dvd.dvd.modEq_zero_nat (dvd_mul_right b T))
  have hzAddMod : z + b * T ≡ z [MOD b] := by
    have := Nat.ModEq.add_left z hmulMod
    simpa [add_assoc] using this

  have hEqMod : z + b * T ≡ b ^ (k + 1) - 1 [MOD b] := by
    show (z + b * T) % b = (b ^ (k + 1) - 1) % b
    simpa [hEq]

  have hzModEq₁ : z ≡ b ^ (k + 1) - 1 [MOD b] := hzAddMod.symm.trans hEqMod

  -- Show `b^(k+1) - 1 ≡ b - 1 [MOD b]` by cancelling `+1`.
  have hbDiv_pow : b ∣ b ^ (k + 1) := dvd_pow_self b (Nat.succ_ne_zero k)
  have hbpow0 : b ^ (k + 1) ≡ 0 [MOD b] := (Dvd.dvd.modEq_zero_nat hbDiv_pow)
  have hb0 : b ≡ 0 [MOD b] := (Dvd.dvd.modEq_zero_nat (dvd_rfl : b ∣ b))
  have hbpowMod : b ^ (k + 1) ≡ b [MOD b] := hbpow0.trans hb0.symm

  have hbEq : b - 1 + 1 = b := Nat.sub_add_cancel hb1
  have hbpowEq : b ^ (k + 1) - 1 + 1 = b ^ (k + 1) := Nat.sub_add_cancel hbpow1

  have hbpowMod' : b ^ (k + 1) - 1 + 1 ≡ b - 1 + 1 [MOD b] := by
    -- rewrite both sides of `hbpowMod` into the `-1 + 1` form
    simpa [hbpowEq, hbEq] using hbpowMod

  have hbMinusMod : b ^ (k + 1) - 1 ≡ b - 1 [MOD b] :=
    Nat.ModEq.add_right_cancel' 1 hbpowMod'

  have hzModEq : z ≡ b - 1 [MOD b] := hzModEq₁.trans hbMinusMod
  have hzmod : z % b = b - 1 := Nat.mod_eq_of_modEq hzModEq hbsub

  -- Let `q = z / b` and use `Nat.mod_add_div` to write `z = (b-1) + b*q`.
  let q : ℕ := z / b

  have hzdecomp : z = (b - 1) + b * q := by
    simpa [q, hzmod, add_assoc, add_left_comm, add_comm] using (Nat.mod_add_div z b).symm

  -- A purely arithmetic identity: `b^(k+1)-1 = (b-1) + b*(b^k-1)`.
  have hgeom : b ^ (k + 1) - 1 = (b - 1) + b * (b ^ k - 1) := by
    apply Nat.add_right_cancel
    have hR : ((b - 1) + b * (b ^ k - 1)) + 1 = b ^ (k + 1) := by
      let X : ℕ := b ^ k - 1
      have h1 : 1 + X = b ^ k := by
        simpa [X, add_assoc, add_left_comm, add_comm] using (Nat.sub_add_cancel hbpowk)
      calc
        ((b - 1) + b * X) + 1
            = (b - 1) + (b * X) + 1 := by simp [add_assoc]
        _ = (b - 1) + 1 + b * X := by
              simp [add_assoc, add_left_comm, add_comm]
        _ = b + b * X := by
              simpa [hbEq, add_assoc]
        _ = b * (1 + X) := by
              simpa [Nat.mul_add, add_assoc]
        _ = b * (b ^ k) := by simpa [h1]
        _ = b ^ (k + 1) := by
              simpa using (pow_succ' b k).symm
    calc
      (b ^ (k + 1) - 1) + 1 = b ^ (k + 1) := Nat.sub_add_cancel hbpow1
      _ = ((b - 1) + b * (b ^ k - 1)) + 1 := by simpa using hR.symm

  -- From `hEq` and `hzdecomp`, deduce `q + T = b^k - 1`.
  have hEq_z : (b - 1) + b * q + b * T = b ^ (k + 1) - 1 := by
    simpa [hzdecomp, add_assoc] using hEq

  have hEq_fact : (b - 1) + b * (q + T) = b ^ (k + 1) - 1 := by
    calc
      (b - 1) + b * (q + T) = (b - 1) + (b * q + b * T) := by
        simp [Nat.mul_add, add_assoc]
      _ = (b - 1) + b * q + b * T := by
        simp [add_assoc]
      _ = b ^ (k + 1) - 1 := hEq_z

  have hEq_compare : (b - 1) + b * (q + T) = (b - 1) + b * (b ^ k - 1) :=
    hEq_fact.trans hgeom

  have hmul_eq : b * (q + T) = b * (b ^ k - 1) := Nat.add_left_cancel hEq_compare
  have hQT : q + T = b ^ k - 1 := by
    exact mul_left_cancel₀ hbne0 hmul_eq

  -- Define the reduced list.
  let e2 : List ℕ := List.replicate q 0 ++ e1.map (fun j => j - 1)

  have hsum_e2 : (e2.map (fun j => b ^ j)).sum = q + T := by
    -- split the sum across the append, and compute each piece
    simp [e2, T, add_assoc, add_left_comm, add_comm]
    rfl

  have hsum2 : (e2.map (fun j => b ^ j)).sum = b ^ k - 1 := by
    calc
      (e2.map (fun j => b ^ j)).sum = q + T := hsum_e2
      _ = b ^ k - 1 := hQT

  -- Length computations.
  have hp : (fun j : ℕ => ! decide (j = 0)) = fun j : ℕ => decide (j ≠ 0) := by
    funext j
    by_cases hj : j = 0 <;> simp [hj]

  have hlen_e : e.length = z + e1.length := by
    have hlen := List.length_eq_length_filter_add (l := e) (f := fun j : ℕ => decide (j = 0))
    simpa [e0, z, e1, hp, add_assoc, add_left_comm, add_comm] using hlen

  have hqle : q ≤ b * q := by
    have h' : q ≤ q * b := le_mul_of_one_le_right (Nat.zero_le q) hb1
    simpa [Nat.mul_comm] using h'

  have hqadd : q + (b - 1) ≤ z := by
    calc
      q + (b - 1) ≤ b * q + (b - 1) := Nat.add_le_add_right hqle (b - 1)
      _ = (b - 1) + b * q := by ac_rfl
      _ = z := by simpa using hzdecomp.symm

  have hlen2 : e2.length + (b - 1) ≤ e.length := by
    calc
      e2.length + (b - 1) = (q + e1.length) + (b - 1) := by
        simp [e2, add_assoc]
      _ = (q + (b - 1)) + e1.length := by ac_rfl
      _ ≤ z + e1.length := Nat.add_le_add_right hqadd e1.length
      _ = e.length := by simpa using hlen_e.symm

  exact ⟨e2, hsum2, hlen2⟩


theorem pow_sub_one_length_lower_bound (b k : ℕ) (hb : 2 ≤ b) (e : List ℕ) :
  (e.map (fun j => b ^ j)).sum = b ^ k - 1 →
  (b - 1) * k ≤ e.length := by
  induction k generalizing e with
  | zero =>
      intro hsum
      simpa using (Nat.zero_le e.length)
  | succ k ih =>
      intro hsum
      have hsum' : (e.map (fun j => b ^ j)).sum = b ^ (k + 1) - 1 := by
        simpa [Nat.succ_eq_add_one] using hsum
      rcases reduce_exponent_list b k hb e hsum' with ⟨e2, hsum2, hlen⟩
      have hklen : (b - 1) * k ≤ e2.length := ih (e := e2) hsum2
      have hstep : (b - 1) * k + (b - 1) ≤ e.length := by
        have h1 : (b - 1) * k + (b - 1) ≤ e2.length + (b - 1) :=
          Nat.add_le_add_right hklen (b - 1)
        exact le_trans h1 hlen
      simpa [Nat.mul_succ] using hstep

theorem replicate_mem_Ball_macro_of_digitsSum (n b : ℕ) (hb : 2 ≤ b) (i : Fin n) (x : ℕ) :
  Multiset.replicate x i ∈ Ball ((Nat.digits b x).sum) (MacroSet n b ∪ A n) := by
  classical
  -- Unfold the definition of `Ball` and use `digitBallList` as the witnessing list.
  simp [Ball]
  refine ⟨digitBallList n b i x, ?_⟩
  refine ⟨?_, ?_⟩
  · -- length bound
    simpa [digitBallList_length n b i x]
  · -- membership + sum
    refine ⟨digitBallList_mem n b hb i x, ?_⟩
    simpa using digitBallList_sum n b hb i x


theorem replicate_mem_Ball_macro_of_log (n b : ℕ) (hb : 2 ≤ b) (i : Fin n) (x : ℕ) :
  Multiset.replicate x i ∈ Ball ((b - 1) * (Nat.log b x + 1)) (MacroSet n b ∪ A n) := by
  have hx : Multiset.replicate x i ∈ Ball ((Nat.digits b x).sum) (MacroSet n b ∪ A n) :=
    replicate_mem_Ball_macro_of_digitsSum n b hb i x
  have hle : (Nat.digits b x).sum ≤ (b - 1) * (Nat.log b x + 1) :=
    digits_sum_le_log_bound b x hb
  exact (Ball_mono_radius n ((Nat.digits b x).sum) ((b - 1) * (Nat.log b x + 1)) (MacroSet n b ∪ A n) hle) hx


theorem ball_inclusion_of_log (n b r s : ℕ) (hb : 2 ≤ b) :
  s ≥ n * (b - 1) * (Nat.log b r + 1) →
    Ball r (A n) ⊆ Ball s (MacroSet n b ∪ A n) := by
  classical
  intro hs
  intro m hm
  -- abbreviations
  let X : Set (FreeAbelianMonoid n) := MacroSet n b ∪ A n
  let R0 : ℕ := (b - 1) * (Nat.log b r + 1)

  have hmcard : m.card ≤ r := (mem_Ball_A_iff_card_le n r m).1 hm

  -- monotonicity of `Ball` in the radius
  have ball_mono : ∀ {R S : ℕ} {m : FreeAbelianMonoid n}, m ∈ Ball R X → R ≤ S → m ∈ Ball S X := by
    intro R S m hm hRS
    rcases hm with ⟨l, hl_len, hl_mem, hl_sum⟩
    exact ⟨l, le_trans hl_len hRS, hl_mem, hl_sum⟩

  -- additivity of `Ball` with respect to `+` and radius addition
  have ball_add : ∀ {R S : ℕ} {m₁ m₂ : FreeAbelianMonoid n},
      m₁ ∈ Ball R X → m₂ ∈ Ball S X → m₁ + m₂ ∈ Ball (R + S) X := by
    intro R S m₁ m₂ hm₁ hm₂
    rcases hm₁ with ⟨l₁, hl₁_len, hl₁_mem, hl₁_sum⟩
    rcases hm₂ with ⟨l₂, hl₂_len, hl₂_mem, hl₂_sum⟩
    refine ⟨l₁ ++ l₂, ?_, ?_, ?_⟩
    · -- length bound
      have hlen : l₁.length + l₂.length ≤ R + S := Nat.add_le_add hl₁_len hl₂_len
      simpa [List.length_append] using hlen
    · -- membership in X
      intro x hx
      have hx' : x ∈ l₁ ∨ x ∈ l₂ := by
        simpa [List.mem_append] using hx
      cases hx' with
      | inl hx₁ => exact hl₁_mem x hx₁
      | inr hx₂ => exact hl₂_mem x hx₂
    · -- sum formula
      simpa [List.sum_append, hl₁_sum, hl₂_sum]

  -- each coordinate multiset belongs to `Ball R0 X`
  have hrep : ∀ i : Fin n, Multiset.replicate (m.count i) i ∈ Ball R0 X := by
    intro i
    have hi :
        Multiset.replicate (m.count i) i ∈
          Ball ((b - 1) * (Nat.log b (m.count i) + 1)) X :=
      replicate_mem_Ball_macro_of_log n b hb i (m.count i)
    have hcount : m.count i ≤ r := le_trans (Multiset.count_le_card i m) hmcard
    have hlog : Nat.log b (m.count i) ≤ Nat.log b r := Nat.log_mono_right hcount
    have hR : (b - 1) * (Nat.log b (m.count i) + 1) ≤ R0 := by
      have : Nat.log b (m.count i) + 1 ≤ Nat.log b r + 1 := Nat.add_le_add_right hlog 1
      simpa [R0] using Nat.mul_le_mul_left (b - 1) this
    exact ball_mono hi hR

  -- sum of the coordinate pieces lies in a ball of radius `card * R0`
  have hsum :
      (∑ i ∈ m.toFinset, Multiset.replicate (m.count i) i) ∈
        Ball (m.toFinset.card * R0) X := by
    classical
    let f : Fin n → FreeAbelianMonoid n := fun i => Multiset.replicate (m.count i) i
    have hf : ∀ i : Fin n, f i ∈ Ball R0 X := by
      intro i
      simpa [f] using hrep i
    -- generalize to an arbitrary finset for induction
    have hsum_aux : ∀ t : Finset (Fin n), (∑ i ∈ t, f i) ∈ Ball (t.card * R0) X := by
      intro t
      refine Finset.induction_on t ?base ?step
      · -- base case
        refine ⟨[], ?_, ?_, ?_⟩
        · simp
        · intro x hx
          cases hx
        · simp
      · intro a s ha_notmem ih
        have ha : f a ∈ Ball R0 X := hf a
        have h_add : (f a + ∑ i ∈ s, f i) ∈ Ball (R0 + s.card * R0) X :=
          ball_add (R := R0) (S := s.card * R0) ha ih
        have h_insert : (∑ i ∈ insert a s, f i) ∈ Ball (R0 + s.card * R0) X := by
          simpa [Finset.sum_insert, ha_notmem] using h_add
        have hrad_le : R0 + s.card * R0 ≤ (insert a s).card * R0 := by
          have hcard : (insert a s).card = s.card + 1 :=
            Finset.card_insert_of_not_mem ha_notmem
          have hEq : R0 + s.card * R0 = (insert a s).card * R0 := by
            calc
              R0 + s.card * R0 = s.card * R0 + R0 := by
                simpa [Nat.add_comm]
              _ = (s.card + 1) * R0 := by
                simpa using (Eq.symm (Nat.succ_mul s.card R0))
              _ = (insert a s).card * R0 := by
                simpa [hcard]
          exact le_of_eq hEq
        exact ball_mono h_insert hrad_le
    simpa [f] using hsum_aux m.toFinset

  -- Bound the radius `m.toFinset.card * R0` by `s`
  have hcard_le_n : m.toFinset.card ≤ n := by
    simpa using (Finset.card_le_univ (s := m.toFinset))
  have hnR0_le_s : n * R0 ≤ s := by
    simpa [R0, Nat.mul_assoc] using hs
  have hrad_le_s : m.toFinset.card * R0 ≤ s := by
    exact le_trans (Nat.mul_le_mul_right R0 hcard_le_n) hnR0_le_s

  have hsum' : (∑ i ∈ m.toFinset, Multiset.replicate (m.count i) i) ∈ Ball s X :=
    ball_mono hsum hrad_le_s

  -- identify the sum with `m`
  have hdecomp : (∑ i ∈ m.toFinset, Multiset.replicate (m.count i) i) = m := by
    simpa [Multiset.nsmul_singleton] using (Multiset.toFinset_sum_count_nsmul_eq (s := m))

  -- finish
  simpa [X, hdecomp] using hsum'

theorem replicate_pow_sub_one_not_mem_Ball_macro (n b k s : ℕ) (hb : 2 ≤ b) (i : Fin n) :
  s < (b - 1) * k →
    Multiset.replicate (b ^ k - 1) i ∉ Ball s (MacroSet n b ∪ A n) := by
  intro hs
  classical
  intro hmem
  rcases hmem with ⟨l, hl_len, hl_mem, hl_sum⟩

  have hb0 : b ≠ 0 := by
    have : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
    exact Nat.ne_of_gt this

  -- A lemma computing counts of the sum of the list.
  have hcount_sum (j : Fin n) :
      (l.map (fun m : Multiset (Fin n) => m.count j)).sum =
        (Multiset.replicate (b ^ k - 1) i).count j := by
    have h :=
        congrArg (fun m : Multiset (Fin n) => (Multiset.countAddMonoidHom j) m) hl_sum
    calc
      (l.map (fun m : Multiset (Fin n) => m.count j)).sum
          = (l.map (fun m : Multiset (Fin n) => (Multiset.countAddMonoidHom j) m)).sum := by
              simp
      _   = (Multiset.countAddMonoidHom j) l.sum := by
              simpa using ((Multiset.countAddMonoidHom j).map_list_sum l).symm
      _   = (Multiset.countAddMonoidHom j) (Multiset.replicate (b ^ k - 1) i) := by
              simpa using h
      _   = (Multiset.replicate (b ^ k - 1) i).count j := by
              simp

  -- Each element of `l.map (fun m => m.count i)` is a power of `b`.
  have hpows :
      (∀ x ∈ l.map (fun m : Multiset (Fin n) => m.count i), ∃ j : ℕ, x = b ^ j) := by
    intro x hx
    rcases (List.mem_map.1 hx) with ⟨m, hm, rfl⟩
    have hmGX : m ∈ MacroSet n b ∪ A n := hl_mem m hm
    rcases mem_MacroSet_union_A_exists_replicate_pow n b m hmGX with ⟨i0, j0, hrep⟩
    subst hrep
    by_cases h0 : i0 = i
    · subst h0
      refine ⟨j0, ?_⟩
      simp
    · exfalso
      -- look at the `i0`-count of the full sum
      have hsum0 : (l.map (fun m : Multiset (Fin n) => m.count i0)).sum = 0 := by
        have := hcount_sum i0
        simpa [Multiset.count_replicate, h0, Ne.symm h0] using this
      have hall : ∀ y ∈ l.map (fun m : Multiset (Fin n) => m.count i0), y = 0 :=
        (List.sum_eq_zero_iff).1 hsum0
      have hm0 : (Multiset.replicate (b ^ j0) i0).count i0 = 0 := by
        have hm' : (Multiset.replicate (b ^ j0) i0).count i0 ∈
            l.map (fun m : Multiset (Fin n) => m.count i0) := by
          exact (List.mem_map.2 ⟨Multiset.replicate (b ^ j0) i0, hm, rfl⟩)
        exact hall _ hm'
      have hm0' : b ^ j0 = 0 := by
        simpa using hm0
      exact (pow_ne_zero j0 hb0) hm0'

  -- The sum of the `i`-counts is `b^k - 1`.
  have hsum_counts : (l.map (fun m : Multiset (Fin n) => m.count i)).sum = b ^ k - 1 := by
    have := hcount_sum i
    simpa using this

  -- Build the corresponding list of exponents.
  let counts : List ℕ := l.map (fun m : Multiset (Fin n) => m.count i)
  have hcounts_pow : ∀ x ∈ counts, ∃ j : ℕ, x = b ^ j := by
    simpa [counts] using hpows

  -- A list of exponents whose `b`-powers are exactly `counts`.
  let e : List ℕ :=
    counts.pmap (fun x hx => Classical.choose hx) (by
      intro x hx
      exact hcounts_pow x hx)

  -- `e` has the same length as `l`.
  have hlen_e : e.length = l.length := by
    simp [e, counts]

  -- Mapping `b^·` over `e` recovers the original `counts` list.
  have hmap_pmap :
      ∀ (cs : List ℕ) (hcs : ∀ x ∈ cs, ∃ j : ℕ, x = b ^ j),
        (cs.pmap (fun x hx => Classical.choose hx) (by
            intro x hx
            exact hcs x hx)).map (fun j => b ^ j) = cs := by
    intro cs hcs
    induction cs with
    | nil =>
        simp
    | cons a t ih =>
        have ha : ∃ j : ℕ, a = b ^ j := hcs a (by simp)
        have ht : ∀ x ∈ t, ∃ j : ℕ, x = b ^ j := by
          intro x hx
          exact hcs x (by simp [hx])
        have ih' :
            (t.pmap (fun x hx => Classical.choose hx) (by
                intro x hx
                exact ht x hx)).map (fun j => b ^ j) = t :=
          ih ht
        -- unfold `List.pmap` on a cons and use `ih'` for the tail.
        simp [List.pmap, ha, ht, ih', (Classical.choose_spec ha).symm]

  have hmap_e : e.map (fun j => b ^ j) = counts := by
    simpa [e] using hmap_pmap counts hcounts_pow

  have hsum_e : (e.map (fun j => b ^ j)).sum = b ^ k - 1 := by
    simpa [hmap_e, counts] using hsum_counts

  have hlen_lower : (b - 1) * k ≤ e.length :=
    pow_sub_one_length_lower_bound b k hb e hsum_e

  have hlen_lower' : (b - 1) * k ≤ l.length := by
    simpa [hlen_e] using hlen_lower

  have hlen_lt : l.length < (b - 1) * k := lt_of_le_of_lt hl_len hs
  exact (Nat.not_lt_of_ge hlen_lower') hlen_lt


theorem hardElement_not_mem_Ball_macro (n b k s : ℕ) (hb : 2 ≤ b) :
  s < n * (b - 1) * k →
    HardElement n b k ∉ Ball s (MacroSet n b ∪ A n) := by
  intro hs
  classical
  cases n with
  | zero =>
      have : False := by
        have : s < 0 := by simpa using hs
        exact Nat.not_lt_zero _ this
      exact this.elim
  | succ n =>
      cases k with
      | zero =>
          have : False := by
            have : s < 0 := by simpa using hs
            exact Nat.not_lt_zero _ this
          exact this.elim
      | succ k =>
          intro hmem
          rcases hmem with ⟨l, hl_len, hl_mem, hl_sum⟩
          let M : ℕ := (b - 1) * Nat.succ k
          have hs' : s < Nat.succ n * M := by
            simpa [M, Nat.mul_assoc] using hs
          have hl_lt : l.length < Nat.succ n * M := lt_of_le_of_lt hl_len hs'
          have get_mem_X (pos : Fin l.length) :
              l.get pos ∈ (MacroSet (Nat.succ n) b ∪ A (Nat.succ n)) := by
            apply hl_mem
            exact List.get_mem l pos
          -- represent each list element as a replicate
          have hrep (pos : Fin l.length) :
              ∃ (i : Fin (Nat.succ n)) (j : ℕ), l.get pos = Multiset.replicate (b ^ j) i :=
            mem_MacroSet_union_A_exists_replicate_pow (Nat.succ n) b (l.get pos) (get_mem_X pos)
          let coord : Fin l.length → Fin (Nat.succ n) := fun pos => Classical.choose (hrep pos)
          have coord_spec (pos : Fin l.length) :
              ∃ j : ℕ, l.get pos = Multiset.replicate (b ^ j) (coord pos) :=
            Classical.choose_spec (hrep pos)
          -- pigeonhole: some coordinate occurs < M times
          have hph :
              ∃ i : Fin (Nat.succ n),
                Finset.card ({x ∈ (Finset.univ : Finset (Fin l.length)) | coord x = i}) < M := by
            have :=
              (Finset.exists_card_fiber_lt_of_card_lt_mul (s := (Finset.univ : Finset (Fin l.length)))
                (t := (Finset.univ : Finset (Fin (Nat.succ n))))
                (f := coord) (n := M)
                (by simpa [Finset.card_univ, M] using hl_lt))
            rcases this with ⟨i, hi, hcard⟩
            refine ⟨i, ?_⟩
            simpa using hcard
          rcases hph with ⟨i0, hi0_lt⟩
          let S : Finset (Fin l.length) := {x ∈ (Finset.univ : Finset (Fin l.length)) | coord x = i0}
          have hS : S.card < M := by simpa [S] using hi0_lt
          let l0 : List (FreeAbelianMonoid (Nat.succ n)) := S.toList.map (fun x => l.get x)
          have hl0_len : l0.length = S.card := by
            simp [l0]
          have hl0_lt : l0.length < M := by
            simpa [hl0_len] using hS
          -- show l0.sum is the big replicate at i0
          have hl0_sum : l0.sum = Multiset.replicate (b ^ Nat.succ k - 1) i0 := by
            -- convenient finset-sum expression for l0.sum
            have hl0sum_finset : l0.sum = ∑ x ∈ S, l.get x := by
              simpa [l0] using
                (Finset.sum_toList (s := S) (f := fun x : Fin l.length => l.get x)).symm
            ext a
            by_cases ha0 : a = i0
            · -- a = i0
              subst a
              -- compute count i0 of l.sum via hl_sum
              have hcount_l : (l.sum).count i0 = b ^ Nat.succ k - 1 := by
                have := congrArg (fun m : FreeAbelianMonoid (Nat.succ n) => m.count i0) hl_sum
                simpa [HardElement, Multiset.count_sum', Multiset.count_replicate] using this
              -- express l.sum as sum over indices
              have hl_sum_univ : (∑ i : Fin l.length, l.get i) = l.sum := by
                simpa using (Fin.sum_univ_getElem l)
              have hl_sum_finset : l.sum = ∑ x ∈ (Finset.univ : Finset (Fin l.length)), l.get x := by
                simpa using hl_sum_univ.symm
              -- count over univ
              have hcount_univ : (l.sum).count i0 = ∑ x ∈ (Finset.univ : Finset (Fin l.length)), (l.get x).count i0 := by
                -- rewrite and use count_sum'
                rw [hl_sum_finset]
                simpa using
                  (Multiset.count_sum' (s := (Finset.univ : Finset (Fin l.length))) (a := i0)
                    (f := fun x : Fin l.length => l.get x))
              -- count over S for l0.sum
              have hcount_l0 : (l0.sum).count i0 = ∑ x ∈ S, (l.get x).count i0 := by
                rw [hl0sum_finset]
                simpa using (Multiset.count_sum' (s := S) (a := i0) (f := fun x => l.get x))
              -- show the univ sum of counts equals the S sum of counts
              have hcount_zero_of_coord_ne (x : Fin l.length) (hx : coord x ≠ i0) : (l.get x).count i0 = 0 := by
                rcases coord_spec x with ⟨j, hj⟩
                rw [hj]
                simp [Multiset.count_replicate, hx]
              have hsum_univ_eq_if :
                  (∑ x ∈ (Finset.univ : Finset (Fin l.length)), (l.get x).count i0) =
                    ∑ x ∈ (Finset.univ : Finset (Fin l.length)),
                      (if coord x = i0 then (l.get x).count i0 else 0) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                by_cases h : coord x = i0
                · -- if_pos
                  rw [if_pos h]
                · -- if_neg
                  have hx0 : (l.get x).count i0 = 0 := hcount_zero_of_coord_ne x h
                  rw [if_neg h]
                  exact hx0
              have hsum_S :
                  (∑ x ∈ S, (l.get x).count i0) =
                    ∑ x ∈ (Finset.univ : Finset (Fin l.length)),
                      (if coord x = i0 then (l.get x).count i0 else 0) := by
                -- Finset.sum_filter gives this
                simpa [S] using
                  (Finset.sum_filter (s := (Finset.univ : Finset (Fin l.length)))
                    (p := fun x : Fin l.length => coord x = i0) (f := fun x => (l.get x).count i0))
              have hsum_univ_eq_S :
                  (∑ x ∈ (Finset.univ : Finset (Fin l.length)), (l.get x).count i0) =
                    ∑ x ∈ S, (l.get x).count i0 := by
                -- combine the previous two equalities
                calc
                  (∑ x ∈ (Finset.univ : Finset (Fin l.length)), (l.get x).count i0)
                      = ∑ x ∈ (Finset.univ : Finset (Fin l.length)),
                          (if coord x = i0 then (l.get x).count i0 else 0) :=
                        hsum_univ_eq_if
                  _ = ∑ x ∈ S, (l.get x).count i0 := by
                        simpa using hsum_S.symm
              -- finish: count i0 on l0.sum equals b^k-1
              have : (l0.sum).count i0 = b ^ Nat.succ k - 1 := by
                -- rewrite via sums
                calc
                  (l0.sum).count i0 = ∑ x ∈ S, (l.get x).count i0 := by
                        simpa [hcount_l0]
                  _ = ∑ x ∈ (Finset.univ : Finset (Fin l.length)), (l.get x).count i0 := by
                        simpa using hsum_univ_eq_S.symm
                  _ = (l.sum).count i0 := by
                        simpa [hcount_univ]
                  _ = b ^ Nat.succ k - 1 := hcount_l
              -- compare with replicate
              simp [Multiset.count_replicate, this]
            · -- a ≠ i0
              have hl0_count : (l0.sum).count a = ∑ x ∈ S, (l.get x).count a := by
                rw [hl0sum_finset]
                simpa using (Multiset.count_sum' (s := S) (a := a) (f := fun x => l.get x))
              have hterm_zero : ∀ x ∈ S, (l.get x).count a = 0 := by
                intro x hx
                have hx' : x ∈ (Finset.univ : Finset (Fin l.length)) ∧ coord x = i0 := by
                  simpa [S] using hx
                have hxcoord : coord x = i0 := hx'.2
                rcases coord_spec x with ⟨j, hj⟩
                have hcx : coord x ≠ a := by
                  intro h
                  apply ha0
                  -- derive a = i0
                  calc
                    a = coord x := h.symm
                    _ = i0 := hxcoord
                rw [hj]
                -- count a in replicate is zero
                simp [Multiset.count_replicate, hcx]
              have hsum_zero : (∑ x ∈ S, (l.get x).count a) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro x hx
                exact hterm_zero x hx
              -- finish
              have : (l0.sum).count a = 0 := by
                calc
                  (l0.sum).count a = ∑ x ∈ S, (l.get x).count a := hl0_count
                  _ = 0 := hsum_zero
              -- replicate count is also 0
              have hia : i0 ≠ a := by
                intro h
                apply ha0
                simpa using h.symm
              simp [Multiset.count_replicate, hia, this]
          have hBall0 : Multiset.replicate (b ^ Nat.succ k - 1) i0 ∈
              Ball l0.length (MacroSet (Nat.succ n) b ∪ A (Nat.succ n)) := by
            refine ⟨l0, le_rfl, ?_, hl0_sum⟩
            intro x hx
            rcases List.mem_map.1 hx with ⟨pos, hpos, rfl⟩
            exact get_mem_X pos
          have hcontra :=
            replicate_pow_sub_one_not_mem_Ball_macro (Nat.succ n) b (Nat.succ k) l0.length hb i0 hl0_lt
          exact hcontra hBall0


theorem theorem_1_place_notation_exponential_expansion (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b) :
  let M := MacroSet n b
  (∃ (d1 d2 : ℝ), 0 < d1 ∧ 0 < d2
      ∧ ∀ (x : ℕ), x ≥ b →
          d1 * Real.log x ≤ (M ∩ (Ball x (A n))).ncard
          ∧ (M ∩ (Ball x (A n))).ncard ≤ d2 * Real.log x)
    ∧
    ∀ s : ℕ, s ≥ 1 →
      (let r1 : ℕ := b ^ (s / (n * (b - 1)) - 1)
       Ball r1 (A n) ⊆ Ball s (M ∪ A n))
      ∧
      (let r2 : ℕ := n * b ^ (s / (n * (b - 1)) + 1)
       ¬ Ball r2 (A n) ⊆ Ball s (M ∪ A n)) := by
  classical
  dsimp
  constructor
  · simpa using (macro_density_bounds n b hn hb)
  · intro s hs
    let q : ℕ := n * (b - 1)
    let t : ℕ := s / q
    constructor
    · -- lower inclusion
      by_cases hqs : q ≤ s
      · -- in this case, t ≥ 1, so we can use ball_inclusion_of_log
        have hqpos : 0 < q := by
          have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0:ℕ) < 1) hn
          have hb1 : 0 < b - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hb)
          exact Nat.mul_pos hn0 hb1
        have ht : 1 ≤ t := by
          have : 1 * q ≤ s := by simpa [one_mul] using hqs
          have : 1 ≤ s / q := (Nat.le_div_iff_mul_le hqpos).2 this
          simpa [t] using this
        have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1:ℕ) < 2) hb
        have hlog : Nat.log b (b ^ (t - 1)) = t - 1 := by
          simpa using (Nat.log_pow hb1 (t - 1))
        have hlog1 : Nat.log b (b ^ (t - 1)) + 1 = t := by
          simpa [hlog, Nat.sub_add_cancel ht]
        have hqt : q * t ≤ s := by
          simpa [t] using (Nat.mul_div_le s q)
        have hineq : s ≥ n * (b - 1) * (Nat.log b (b ^ (t - 1)) + 1) := by
          -- rewrite RHS to q * t
          have : n * (b - 1) * (Nat.log b (b ^ (t - 1)) + 1) = q * t := by
            simp [q, hlog1, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          -- now
          simpa [this] using hqt
        have hinc : Ball (b ^ (t - 1)) (A n) ⊆ Ball s (MacroSet n b ∪ A n) :=
          ball_inclusion_of_log (n := n) (b := b) (r := b ^ (t - 1)) (s := s) hb hineq
        -- match the let-bound r1
        simpa [q, t] using hinc
      · -- if q > s, then t = 0 and r1 = 1; inclusion is trivial by reusing the witness list
        have hlt : s < q := lt_of_not_ge hqs
        have ht0 : t = 0 := by
          exact Nat.div_eq_of_lt hlt
        have hinc : Ball (b ^ (t - 1)) (A n) ⊆ Ball s (MacroSet n b ∪ A n) := by
          intro m hm
          rcases hm with ⟨l, hl, hA, hsum⟩
          have hr1 : b ^ (t - 1) = 1 := by
            simp [ht0]
          have hl1 : l.length ≤ 1 := by
            simpa [hr1] using hl
          have hls : l.length ≤ s := le_trans hl1 hs
          refine ⟨l, hls, ?_, hsum⟩
          intro x hx
          exact Or.inr (hA x hx)
        simpa [q, t] using hinc
    · -- upper non-inclusion
      -- we will use HardElement with k = t + 1
      let k : ℕ := t + 1
      have hqpos : 0 < q := by
        have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0:ℕ) < 1) hn
        have hb1 : 0 < b - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hb)
        exact Nat.mul_pos hn0 hb1
      have hslt : s < n * (b - 1) * k := by
        -- show s < q * (t + 1) using the characterization of division
        have hslt' : s < q * (t + 1) := by
          -- prove by contradiction using le_div_iff_mul_le
          apply lt_of_not_ge
          intro hle
          have hle' : (t + 1) * q ≤ s := by
            -- commute multiplication
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hle
          have hdiv : t + 1 ≤ s / q := (Nat.le_div_iff_mul_le hqpos).2 hle'
          have hcontra : t + 1 ≤ t := by
            simpa [t] using hdiv
          have : Nat.succ t ≤ t := by
            simpa [Nat.succ_eq_add_one] using hcontra
          exact (Nat.not_succ_le_self t) this
        -- rewrite q and k
        simpa [q, k, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hslt'
      have hin : HardElement n b k ∈ Ball (n * b ^ k) (A n) := hardElement_mem_Ball_A n b k
      have hnot : HardElement n b k ∉ Ball s (MacroSet n b ∪ A n) :=
        hardElement_not_mem_Ball_macro n b k s hb hslt
      -- show the negation of inclusion
      intro hsub
      exact hnot (hsub (by simpa [q, t, k] using hin))


theorem zero_mem_Ball (n : ℕ) (R : ℕ) (X : Set (FreeAbelianMonoid n)) : (0 : FreeAbelianMonoid n) ∈ Ball R X := by
  classical
  -- unfold membership in `Ball` and use the empty list as witness
  refine ⟨[], ?_⟩
  refine ⟨?_, ?_⟩
  · simpa using (Nat.zero_le R)
  · refine ⟨?_, ?_⟩
    · intro x hx
      cases hx
    · simp [FreeAbelianMonoid]

