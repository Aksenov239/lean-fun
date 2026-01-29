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

theorem theorem_1_place_notation_exponential_expansion
  (n b : ℕ)
  (hb : 2 ≤ b) :
  let M := MacroSet n b
  (∃ (d1 d2 : ℕ), ∀ (x : ℕ), (x ≥ 2) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log x) ≤ (M ∩ (Ball x (A n))).ncard
      ∧ (M ∩ (Ball x (A n))).ncard ≤ d2 * (Real.log x))
    ∧
    ∀ s : ℕ, s ≥ 1 → (
      let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
      (Ball r1 (A n) ⊆ (Ball s (M ∪ (A n))))
      ∧
      let r2 := 1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (n - 1)) - 1))
      ¬ (Ball r2 (A n) ⊆ (Ball s (M ∪ (A n))))) :=
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
  Set.range (fun i : Fin n => ({i} : Multiset (Fin n)))

theorem A_ncard (n : ℕ) : (A n).ncard = n := by
  classical
  -- `A n` is the range of the singleton map `Fin n → Multiset (Fin n)`.
  simpa [A, Nat.card_fin] using
    (Set.ncard_range_of_injective (f := fun i : Fin n => ({i} : Multiset (Fin n)))
      (by
        intro a b h
        exact (Multiset.singleton_inj.mp h)))

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) : Set (FreeAbelianMonoid n) :=
  {m | ∃ l : List (FreeAbelianMonoid n), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

theorem Ball_mono {n R : ℕ} {X Y : Set (FreeAbelianMonoid n)} : X ⊆ Y → Ball R X ⊆ Ball R Y := by
  intro hXY
  intro m hm
  unfold Ball at hm ⊢
  rcases hm with ⟨l, hlR, hlX, rfl⟩
  refine ⟨l, hlR, ?_, rfl⟩
  intro x hx
  exact hXY (hlX x hx)


theorem Ball_mono_radius {n : ℕ} {R S : ℕ} {X : Set (FreeAbelianMonoid n)} : R ≤ S → Ball R X ⊆ Ball S X := by
  intro hRS
  intro m hm
  rcases hm with ⟨l, hl, hX, hsum⟩
  refine ⟨l, ?_, hX, hsum⟩
  exact le_trans hl hRS


theorem Nat_card_vector_eq_pow {α : Type*} [Fintype α] (n : ℕ) : Nat.card (List.Vector α n) = (Fintype.card α) ^ n := by
  classical
  rw [Nat.card_eq_fintype_card]
  simpa using (card_vector (α := α) n)


theorem exists_K0_mul_pow_lt_two_pow (A : ℝ) (hA : 0 ≤ A) (m : ℕ) :
  ∃ K0 : ℕ, ∀ K ≥ K0, A * ((K + 1 : ℕ) : ℝ) ^ m < (2 : ℝ) ^ K := by
  classical
  by_cases hAz : A = 0
  · refine ⟨0, ?_⟩
    intro K hK
    subst hAz
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    simpa using (pow_pos h2 K)
  · -- We show that (A * (K+1)^m) / 2^K → 0, hence it is eventually < 1.
    have hlim0 :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ) ^ m) / (2 : ℝ) ^ n) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (tendsto_pow_const_div_const_pow_of_one_lt m (r := (2 : ℝ)) (by norm_num))
    have hlim1 :
        Filter.Tendsto (fun K : ℕ => (((K + 1 : ℕ) : ℝ) ^ m) / (2 : ℝ) ^ (K + 1)) Filter.atTop
          (nhds (0 : ℝ)) := by
      -- shift by 1
      have :=
        (Filter.tendsto_add_atTop_iff_nat
              (f := fun n : ℕ => ((n : ℝ) ^ m) / (2 : ℝ) ^ n)
              (l := nhds (0 : ℝ)) 1).2
          hlim0
      simpa using this
    have hlim2 :
        Filter.Tendsto (fun K : ℕ => ((K : ℝ) + 1) ^ m / (2 : ℝ) ^ K) Filter.atTop (nhds (0 : ℝ)) := by
      -- remove the shift in the denominator by multiplying by 2
      have hconst :
          Filter.Tendsto (fun K : ℕ => (2 : ℝ) * (((K : ℝ) + 1) ^ m / (2 : ℝ) ^ (K + 1)))
            Filter.atTop (nhds (0 : ℝ)) := by
        -- `hlim1` already has the numerator `((K+1):ℕ)`; simplify it to `↑K + 1`
        simpa using (Filter.Tendsto.const_mul (b := (2 : ℝ)) hlim1)
      have hfun :
          (fun K : ℕ => ((K : ℝ) + 1) ^ m / (2 : ℝ) ^ K) =
            (fun K : ℕ => (2 : ℝ) * (((K : ℝ) + 1) ^ m / (2 : ℝ) ^ (K + 1))) := by
        funext K
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        simp [div_eq_mul_inv, pow_succ, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev, h2]
      simpa [hfun] using hconst
    have hlimF :
        Filter.Tendsto (fun K : ℕ => (A * (((K : ℝ) + 1) ^ m)) / (2 : ℝ) ^ K) Filter.atTop
          (nhds (0 : ℝ)) := by
      -- multiply by the constant `A`
      have hconst := (Filter.Tendsto.const_mul (b := A) hlim2)
      -- rewrite `A * (x / y)` as `(A * x) / y`
      simpa [mul_div_assoc] using hconst
    have h_event : ∀ᶠ K : ℕ in Filter.atTop,
        (A * (((K : ℝ) + 1) ^ m)) / (2 : ℝ) ^ K < (1 : ℝ) := by
      exact
        (Filter.Tendsto.eventually_lt_const (u := (1 : ℝ)) (v := (0 : ℝ)) (by norm_num) hlimF)
    rcases (Filter.eventually_atTop.1 h_event) with ⟨K0, hK0⟩
    refine ⟨K0, ?_⟩
    intro K hK
    have hlt : (A * (((K : ℝ) + 1) ^ m)) / (2 : ℝ) ^ K < (1 : ℝ) := hK0 K hK
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ K := pow_pos h2pos K
    -- clear the denominator
    have : A * (((K : ℝ) + 1) ^ m) < (2 : ℝ) ^ K := (div_lt_one hpowpos).1 hlt
    -- rewrite `↑K + 1` as `(K+1 : ℕ)` cast
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using this

theorem exists_list_subtype_val_eq_of_forall_mem {α : Type*} {X : Set α} (l : List α) :
  (∀ x ∈ l, x ∈ X) → ∃ lX : List X, lX.map ((↑) : X → α) = l := by
  intro h
  have hr : l ∈ Set.range (List.map ((↑) : X → α)) := by
    simpa [Set.range_list_map_coe (s := X)] using
      (show l ∈ ({l : List α | ∀ x ∈ l, x ∈ X} : Set (List α)) from h)
  simpa [Set.range] using hr


theorem Ball_finite_of_finite {n R : ℕ} {X : Set (FreeAbelianMonoid n)} : X.Finite → (Ball R X).Finite := by
  intro hX
  classical
  letI : Fintype X := hX.fintype
  let S : Set (List X) := {l | l.length ≤ R}
  have hS : S.Finite := by
    simpa [S] using (List.finite_length_le (α := X) R)
  let f : List X → FreeAbelianMonoid n := fun l => l.unattach.sum
  have hImage : (f '' S).Finite := hS.image f
  refine hImage.subset ?_
  intro m hm
  rcases hm with ⟨l, hlR, hmem, hsum⟩
  -- build a list of elements of X from l
  let lX : List X :=
    l.pmap (fun x hx => (⟨x, hx⟩ : X)) (by
      intro x hx
      exact hmem x hx)
  refine ⟨lX, ?_, ?_⟩
  · -- lX ∈ S
    have : lX.length = l.length := by simp [lX]
    simpa [S, this] using hlR
  · -- f lX = m
    have hval' : ∀ (l : List (FreeAbelianMonoid n))
        (h : ∀ x ∈ l, x ∈ X),
        (List.pmap (fun x hx => (⟨x, hx⟩ : X)) l h).unattach = l := by
      intro l
      induction l with
      | nil =>
          intro h
          simp
      | cons a t ih =>
          intro h
          have ha : a ∈ X := h a (by simp)
          have ht : ∀ x ∈ t, x ∈ X := by
            intro x hx
            exact h x (by simp [hx])
          simp [List.pmap, ha, ht, ih ht]
    have hval : lX.unattach = l := by
      simpa [lX] using hval' l (by
        intro x hx
        exact hmem x hx)
    simpa [f, hval, hsum]


theorem ncard_range_le_nat_card {α β : Type*} [Finite α] (f : α → β) : (Set.range f).ncard ≤ Nat.card α := by
  classical
  -- Rewrite range as image of univ and apply cardinality bound on images.
  simpa [Set.image_univ] using (Set.ncard_image_le (f := f) (s := (Set.univ : Set α)))

theorem Ball_ncard_upper {n s : ℕ} (X : Set (FreeAbelianMonoid n)) (hX : X.Finite) : (Ball s X).ncard ≤ (X.ncard + 1) ^ s := by
  classical
  -- Use the finite set `Y := X ∪ {0}` and sum maps from vectors of length `s`.
  let α := FreeAbelianMonoid n
  let Y : Set α := X ∪ {0}
  have hY : Y.Finite := by
    simpa [Y] using hX.union (Set.finite_singleton (0 : α))
  haveI : Fintype Y := hY.fintype

  -- Map a length-`s` vector over `Y` to the sum of its entries.
  let f : List.Vector Y s → α := fun v => (v.toList.map (fun x : Y => (x : α))).sum

  -- Every element of `Ball s X` is in the range of this map.
  have hBall_range : Ball s X ⊆ Set.range f := by
    intro m hm
    rcases hm with ⟨l, hl, hlX, rfl⟩
    -- Pad `l` with zeros to length exactly `s`.
    let l' : List α := l ++ List.replicate (s - l.length) (0 : α)
    have hl'len : l'.length = s := by
      dsimp [l']
      simp [List.length_append, hl, Nat.add_sub_of_le hl]
    have hl'sum : l'.sum = l.sum := by
      dsimp [l']
      simp [List.sum_append, List.sum_replicate]
    have hl'mem : ∀ x ∈ l', x ∈ Y := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact Or.inl (hlX x hx)
      ·
        have hx0 : x = (0 : α) := by
          have hx' : (s - l.length) ≠ 0 ∧ x = (0 : α) := by
            simpa [List.mem_replicate] using hx
          exact hx'.2
        subst hx0
        simp [Y]
    obtain ⟨lY, hlYmap⟩ :=
      exists_list_subtype_val_eq_of_forall_mem (X := Y) l' (by
        intro x hx
        exact hl'mem x hx)
    have hlYlen : lY.length = s := by
      have := congrArg List.length hlYmap
      simpa [hl'len] using this
    let v : List.Vector Y s := ⟨lY, hlYlen⟩
    refine ⟨v, ?_⟩
    dsimp [f]
    have hmap : v.toList.map (fun x : Y => (x : α)) = l' := by
      simpa [v] using hlYmap
    calc
      (v.toList.map (fun x : Y => (x : α))).sum = l'.sum := by
        simpa [hmap]
      _ = l.sum := by
        simpa [hl'sum]

  have hRangeFin : (Set.range f).Finite := by
    exact Set.finite_range f

  have h1 : (Ball s X).ncard ≤ (Set.range f).ncard :=
    Set.ncard_le_ncard hBall_range hRangeFin

  have h2 : (Set.range f).ncard ≤ Nat.card (List.Vector Y s) := by
    simpa using (ncard_range_le_nat_card f)

  -- Compute the cardinality of `List.Vector Y s`.
  have hcardVec : Nat.card (List.Vector Y s) = (Fintype.card Y) ^ s := by
    simpa using (Nat_card_vector_eq_pow (α := Y) s)

  -- Relate `Fintype.card Y` to `X.ncard + 1`.
  have hYcard_eq : Fintype.card Y = Y.ncard := by
    have h1' : Y.ncard = Y.toFinset.card := Set.ncard_eq_toFinset_card' (s := Y)
    have h2' : Y.toFinset.card = Fintype.card Y := Set.toFinset_card (s := Y)
    exact (h1'.trans h2').symm

  have hYncard : Y.ncard ≤ X.ncard + 1 := by
    simpa [Y, Set.ncard_singleton] using
      (Set.ncard_union_le (s := X) (t := ({0} : Set α)))

  have hYle : Fintype.card Y ≤ X.ncard + 1 := by
    simpa [hYcard_eq] using hYncard

  have hpow : (Fintype.card Y) ^ s ≤ (X.ncard + 1) ^ s := by
    simpa using (pow_le_pow_left' hYle s)

  -- Put everything together.
  calc
    (Ball s X).ncard ≤ (Set.range f).ncard := h1
    _ ≤ Nat.card (List.Vector Y s) := h2
    _ = (Fintype.card Y) ^ s := hcardVec
    _ ≤ (X.ncard + 1) ^ s := hpow

theorem one_le_log_exp1_add_nat (r : ℕ) : 1 ≤ Real.log (Real.exp 1 + (r : ℝ)) := by
  have hx : (0 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_pos 1
  have hxy : Real.exp 1 ≤ Real.exp 1 + (r : ℝ) := by
    have hr : (0 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.zero_le r)
    simpa [add_comm, add_left_comm, add_assoc] using (le_add_of_nonneg_right hr)
  have hlog : Real.log (Real.exp 1) ≤ Real.log (Real.exp 1 + (r : ℝ)) := by
    exact Real.log_le_log hx hxy
  simpa [Real.log_exp] using hlog

noncomputable def rKS (K s : ℕ) : ℕ :=
  1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))

theorem exp_lt_rKS (K s : ℕ) :
  Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ)) < (rKS K s : ℝ) := by
  -- main inequality is `exp t < floorNat (exp t) + 1`, then rewrite `rKS`
  simpa [rKS, Int.floor_toNat, add_comm, add_left_comm, add_assoc] using
    (Nat.lt_floor_add_one (Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ))))

theorem rKS_le_exp_add_one (K s : ℕ) :
  (rKS K s : ℝ) ≤ Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ)) + 1 := by
  classical
  unfold rKS
  set t : ℝ := (K : ℝ) * (s : ℝ) * Real.log (s : ℝ)
  have ht' : (K * s : ℝ) * Real.log (s : ℝ) = t := by
    simp [t, mul_assoc, Nat.cast_mul]
  have hfloor : (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp t := by
    exact Nat.floor_le (Real.exp_nonneg t)
  -- rewrite the goal in terms of t
  -- first, rewrite the exp inside rKS
  have hexp : Real.exp (K * s * Real.log s) = Real.exp t := by
    -- unfold coercions
    -- K*s*log s is (K*s:ℝ) * log (s:ℝ)
    simpa [mul_assoc, ht', t]
  -- use the floor inequality
  -- convert Int.toNat (Int.floor _) to Nat.floor
  -- and add 1
  have hmain : (1 : ℝ) + (⌊Real.exp t⌋₊ : ℝ) ≤ Real.exp t + 1 := by
    linarith
  -- finish by simp
  -- goal: (↑(1 + Int.toNat (Int.floor (Real.exp (K * s * Real.log s)))) : ℝ) ≤ Real.exp t + 1
  -- rewrite floor part
  --
  --
  simpa [t, Int.floor_toNat, hexp, add_assoc, add_left_comm, add_comm, Nat.cast_add] using hmain

theorem exp1_add_rKS_le_mul_exp (K s : ℕ) (hs : 2 ≤ s) :
  (Real.exp 1 + (rKS K s : ℝ)) ≤ (Real.exp 1 + 3) * Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ)) := by
  classical
  set t : ℝ := (K : ℝ) * (s : ℝ) * Real.log (s : ℝ)
  set x : ℝ := Real.exp t

  have hrKS : (rKS K s : ℝ) ≤ x + 1 := by
    simpa [t, x] using (rKS_le_exp_add_one K s)

  have hstep : Real.exp 1 + (rKS K s : ℝ) ≤ Real.exp 1 + (x + 1) := by
    linarith [hrKS]

  -- show `0 ≤ t` using `hs : 2 ≤ s`
  have hs1 : (1 : ℕ) ≤ s := le_trans (by decide : (1 : ℕ) ≤ 2) hs
  have hlog : 0 ≤ Real.log (s : ℝ) := by
    have hs1R : (1 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs1
    simpa using Real.log_nonneg hs1R

  have ht : 0 ≤ t := by
    have hK : 0 ≤ (K : ℝ) := by
      exact_mod_cast (Nat.zero_le K)
    have hS : 0 ≤ (s : ℝ) := by
      exact_mod_cast (Nat.zero_le s)
    have : 0 ≤ (K : ℝ) * (s : ℝ) * Real.log (s : ℝ) := by
      exact mul_nonneg (mul_nonneg hK hS) hlog
    simpa [t] using this

  have hx1 : (1 : ℝ) ≤ x := by
    simpa [x] using Real.one_le_exp ht
  have hx0 : 0 ≤ x := by
    have : 0 < Real.exp t := Real.exp_pos t
    simpa [x] using le_of_lt this

  -- key algebraic inequality
  have hkey : Real.exp 1 + (x + 1) ≤ (Real.exp 1 + 3) * x := by
    have hA0 : 0 ≤ Real.exp 1 + 1 := by
      have hpos : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
      linarith

    have hmul1 : Real.exp 1 + 1 ≤ (Real.exp 1 + 1) * x := by
      simpa [one_mul] using (mul_le_mul_of_nonneg_left hx1 hA0)

    have hmul2 : (Real.exp 1 + 1) * x ≤ (Real.exp 1 + 2) * x := by
      have hconst : Real.exp 1 + 1 ≤ Real.exp 1 + 2 := by linarith
      exact mul_le_mul_of_nonneg_right hconst hx0

    have hmul : Real.exp 1 + 1 ≤ (Real.exp 1 + 2) * x := le_trans hmul1 hmul2

    calc
      Real.exp 1 + (x + 1) = x + (Real.exp 1 + 1) := by ring
      _ ≤ x + (Real.exp 1 + 2) * x := by
        -- `add_le_add_right` adds on the left; `simp` fixes commutativity if needed
        simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hmul x)
      _ = (Real.exp 1 + 3) * x := by ring

  have : Real.exp 1 + (rKS K s : ℝ) ≤ (Real.exp 1 + 3) * x :=
    le_trans hstep hkey

  simpa [t, x] using this


theorem loglog_exp1_add_r_bound (K s : ℕ) (hK : 2 ≤ K) (hs : 2 ≤ s) :
  Real.log (Real.log (Real.exp 1 + (rKS K s : ℝ))) ≤ Real.log ((Real.exp 1 + 3) * (2 * (K : ℝ)) * (s : ℝ) ^ 2) := by
  classical
  -- set up notation
  set t : ℝ := (K : ℝ) * (s : ℝ) * Real.log (s : ℝ) with ht
  have hmain : Real.exp 1 + (rKS K s : ℝ) ≤ (Real.exp 1 + 3) * Real.exp t := by
    simpa [t, ht] using exp1_add_rKS_le_mul_exp K s hs
  -- take logs once
  have hx : 0 < Real.exp 1 + (rKS K s : ℝ) := by
    positivity
  have hlog1 : Real.log (Real.exp 1 + (rKS K s : ℝ)) ≤ Real.log ((Real.exp 1 + 3) * Real.exp t) := by
    exact Real.log_le_log hx hmain
  -- rewrite the RHS log
  have hlog1' : Real.log (Real.exp 1 + (rKS K s : ℝ)) ≤ Real.log (Real.exp 1 + 3) + t := by
    have hne1 : (Real.exp 1 + 3 : ℝ) ≠ 0 := by
      have : (0 : ℝ) < Real.exp 1 + 3 := by positivity
      exact ne_of_gt this
    have hne2 : Real.exp t ≠ 0 := by
      exact ne_of_gt (Real.exp_pos t)
    -- use log_mul + log_exp
    simpa [Real.log_mul hne1 hne2, Real.log_exp, add_assoc] using hlog1
  -- bound t by K*s^2
  have ht_le : t ≤ (K : ℝ) * (s : ℝ) ^ 2 := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (Nat.zero_le s)
    have hlog_le : Real.log (s : ℝ) ≤ (s : ℝ) := by
      exact Real.log_le_self hs0
    have hKs0 : (0 : ℝ) ≤ (K : ℝ) * (s : ℝ) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hlog_le hKs0
    -- (K*s) * log s ≤ (K*s) * s
    simpa [t, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  -- combine to get an upper bound on log(exp1+rKS)
  have hlog_le_big : Real.log (Real.exp 1 + (rKS K s : ℝ)) ≤ (Real.exp 1 + 3) * (2 * (K : ℝ)) * (s : ℝ) ^ 2 := by
    have h1 : Real.log (Real.exp 1 + (rKS K s : ℝ)) ≤ Real.log (Real.exp 1 + 3) + (K : ℝ) * (s : ℝ) ^ 2 := by
      have h2 : Real.log (Real.exp 1 + 3) + t ≤ Real.log (Real.exp 1 + 3) + (K : ℝ) * (s : ℝ) ^ 2 := by
        -- add the same constant on the left, then commute
        have h2' := add_le_add_right ht_le (Real.log (Real.exp 1 + 3))
        -- h2' : t + log ≤ K*s^2 + log
        simpa [add_comm, add_left_comm, add_assoc] using h2'
      exact le_trans hlog1' h2
    have hlog_const : Real.log (Real.exp 1 + 3) ≤ Real.exp 1 + 3 := by
      have : (0 : ℝ) ≤ Real.exp 1 + 3 := by positivity
      exact Real.log_le_self this
    have hKs2_ge1 : (1 : ℝ) ≤ (K : ℝ) * (s : ℝ) ^ 2 := by
      have hK1 : (1 : ℕ) ≤ K := le_trans (by decide : (1 : ℕ) ≤ 2) hK
      have hs1 : (1 : ℕ) ≤ s := le_trans (by decide : (1 : ℕ) ≤ 2) hs
      have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      have hs1R : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
      have hs2_ge1 : (1 : ℝ) ≤ (s : ℝ) ^ 2 := by
        nlinarith [hs1R]
      nlinarith [hK1R, hs2_ge1]
    have hconst_mul : Real.exp 1 + 3 ≤ (Real.exp 1 + 3) * ((K : ℝ) * (s : ℝ) ^ 2) := by
      have hpos : (0 : ℝ) < Real.exp 1 + 3 := by positivity
      have := mul_le_mul_of_nonneg_left hKs2_ge1 (le_of_lt hpos)
      -- rewrite 1 * (exp1+3)
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hlog_le_mul : Real.log (Real.exp 1 + 3) ≤ (Real.exp 1 + 3) * ((K : ℝ) * (s : ℝ) ^ 2) := by
      exact le_trans hlog_const hconst_mul
    have hKs2_le_mul : (K : ℝ) * (s : ℝ) ^ 2 ≤ (Real.exp 1 + 3) * ((K : ℝ) * (s : ℝ) ^ 2) := by
      have hpos : (0 : ℝ) ≤ (K : ℝ) * (s : ℝ) ^ 2 := by positivity
      have hone : (1 : ℝ) ≤ Real.exp 1 + 3 := by
        have : (0 : ℝ) ≤ Real.exp 1 + 2 := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right hone hpos
      -- rewrite
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hsum : Real.log (Real.exp 1 + 3) + (K : ℝ) * (s : ℝ) ^ 2 ≤
        (Real.exp 1 + 3) * ((K : ℝ) * (s : ℝ) ^ 2) + (Real.exp 1 + 3) * ((K : ℝ) * (s : ℝ) ^ 2) := by
      exact add_le_add hlog_le_mul hKs2_le_mul
    have hsum' : (Real.exp 1 + 3) * ((K : ℝ) * (s : ℝ) ^ 2) + (Real.exp 1 + 3) * ((K : ℝ) * (s : ℝ) ^ 2) =
        (Real.exp 1 + 3) * (2 * (K : ℝ)) * (s : ℝ) ^ 2 := by
      ring
    exact le_trans h1 (by simpa [hsum'] using hsum)
  -- positivity of inner log
  have hlog_pos : 0 < Real.log (Real.exp 1 + (rKS K s : ℝ)) := by
    have h1' : (1 : ℝ) < Real.exp 1 + (rKS K s : ℝ) := by
      have hexp : (1 : ℝ) < Real.exp 1 := by
        have : (0 : ℝ) < (1 : ℝ) := by norm_num
        simpa using (Real.one_lt_exp_iff).2 this
      have hr : (0 : ℝ) ≤ (rKS K s : ℝ) := by
        exact_mod_cast (Nat.zero_le (rKS K s))
      linarith
    exact Real.log_pos h1'
  -- take logs again
  exact Real.log_le_log hlog_pos hlog_le_big

theorem log_exp1_add_rKS_le_mul (K s : ℕ) (hK : 2 ≤ K) (hs : 2 ≤ s) :
  Real.log (Real.exp 1 + (rKS K s : ℝ)) ≤ (Real.exp 1 + 3) * (2 * (K : ℝ)) * (s : ℝ) ^ 2 := by
  classical
  set A : ℝ := Real.exp 1 + (rKS K s : ℝ)
  set C : ℝ := (Real.exp 1 + 3) * (2 * (K : ℝ)) * (s : ℝ) ^ 2
  have hloglog : Real.log (Real.log A) ≤ Real.log C := by
    simpa [A, C] using loglog_exp1_add_r_bound K s hK hs
  have hA1 : (1 : ℝ) < A := by
    have h1exp : (1 : ℝ) < Real.exp 1 := by
      have h01 : (0 : ℝ) < (1 : ℝ) := by
        norm_num
      have h := (Real.exp_lt_exp).2 h01
      simpa using h
    have hr0 : 0 ≤ (rKS K s : ℝ) := by
      exact_mod_cast (Nat.zero_le (rKS K s))
    have hexp_le : Real.exp 1 ≤ Real.exp 1 + (rKS K s : ℝ) := by
      exact le_add_of_nonneg_right hr0
    have : (1 : ℝ) < Real.exp 1 + (rKS K s : ℝ) := lt_of_lt_of_le h1exp hexp_le
    simpa [A] using this
  have hlogApos : 0 < Real.log A := by
    exact Real.log_pos hA1
  have hCpos : 0 < C := by
    have hEpos : 0 < Real.exp 1 + 3 := by
      have h3 : (0 : ℝ) < 3 := by
        norm_num
      exact add_pos (Real.exp_pos (1 : ℝ)) h3
    have hKnat : 0 < K := by
      exact lt_of_lt_of_le Nat.zero_lt_two hK
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      exact_mod_cast hKnat
    have h2pos : (0 : ℝ) < (2 : ℝ) := by
      norm_num
    have h2Kpos : 0 < 2 * (K : ℝ) := by
      exact mul_pos h2pos hKpos
    have hsNat : 0 < s := by
      exact lt_of_lt_of_le Nat.zero_lt_two hs
    have hspos : (0 : ℝ) < (s : ℝ) := by
      exact_mod_cast hsNat
    have hs2pos : 0 < (s : ℝ) ^ 2 := by
      simpa using (pow_pos hspos 2)
    have hfirst : 0 < (Real.exp 1 + 3) * (2 * (K : ℝ)) := by
      exact mul_pos hEpos h2Kpos
    have : 0 < (Real.exp 1 + 3) * (2 * (K : ℝ)) * (s : ℝ) ^ 2 := by
      exact mul_pos hfirst hs2pos
    simpa [C] using this
  have h_exp : Real.exp (Real.log (Real.log A)) ≤ Real.exp (Real.log C) := by
    exact Real.exp_monotone hloglog
  have hx : Real.exp (Real.log (Real.log A)) = Real.log A := by
    simpa using (Real.exp_log hlogApos)
  have hy : Real.exp (Real.log C) = C := by
    simpa using (Real.exp_log hCpos)
  have hfinal : Real.log A ≤ C := by
    simpa [hx, hy] using h_exp
  simpa [A, C] using hfinal

theorem rpow_le_pow_natCeil_abs (x q : ℝ) (hx : 1 ≤ x) : Real.rpow x q ≤ x ^ (Nat.ceil |q|) := by
  classical
  set m : ℕ := Nat.ceil |q| with hm
  have hq : q ≤ (m : ℝ) := by
    have h1 : q ≤ |q| := le_abs_self q
    have h2 : |q| ≤ (Nat.ceil |q| : ℝ) := by
      simpa using (Nat.le_ceil (|q|))
    have h2' : |q| ≤ (m : ℝ) := by
      simpa [hm] using h2
    exact le_trans h1 h2'
  have h := Real.rpow_le_rpow_of_exponent_le (x := x) (y := q) (z := (m : ℝ)) hx hq
  -- rewrite the RHS using `Real.rpow_natCast`
  simpa [hm, Real.rpow_natCast] using h

theorem c_rpow_log_exp1_add_rKS_le (c q : ℝ) (hc : 0 ≤ c) (K s : ℕ) (hK : 2 ≤ K) (hs : 2 ≤ s) :
  let m : ℕ := Nat.ceil |q|
  c * Real.rpow (Real.log (Real.exp 1 + (rKS K s : ℝ))) q ≤
    (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
  classical
  dsimp
  -- set m = ceil |q|
  set m : ℕ := Nat.ceil |q| with hm
  -- rewrite occurrences of Nat.ceil |q| to m
  simp [hm.symm]
  -- abbreviate x
  set x : ℝ := Real.log (Real.exp 1 + (rKS K s : ℝ)) with hx
  -- rewrite x in goal
  simp [hx.symm]
  -- basic bound: 1 ≤ x
  have hx1 : 1 ≤ x := by
    simpa [hx.symm] using one_le_log_exp1_add_nat (rKS K s)
  have hx0 : 0 ≤ x := by
    linarith
  -- rpow bound
  have hrpow : Real.rpow x q ≤ x ^ m := by
    simpa [hm.symm] using rpow_le_pow_natCeil_abs x q hx1
  have hcrpow : c * Real.rpow x q ≤ c * x ^ m := by
    exact mul_le_mul_of_nonneg_left hrpow hc
  -- bound on log ...
  let B : ℝ := (Real.exp 1 + 3) * (2 * (K : ℝ)) * (s : ℝ) ^ 2
  have hxB : x ≤ B := by
    simpa [B, hx.symm] using log_exp1_add_rKS_le_mul K s hK hs
  have hpow : x ^ m ≤ B ^ m := by
    exact pow_le_pow_left₀ hx0 hxB m
  have hcxm : c * x ^ m ≤ c * B ^ m := by
    exact mul_le_mul_of_nonneg_left hpow hc
  have hleft : c * Real.rpow x q ≤ c * B ^ m := le_trans hcrpow hcxm
  -- now expand B^m and bound (2*K)^m
  have hKle : (K : ℝ) ≤ (K : ℝ) + 1 := by
    linarith
  have h2Kle : (2 * (K : ℝ)) ≤ (2 * ((K : ℝ) + 1)) := by
    have h2nonneg : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_le_mul_of_nonneg_left hKle h2nonneg
  have h2Kpow : (2 * (K : ℝ)) ^ m ≤ (2 * ((K : ℝ) + 1)) ^ m := by
    have h2Knonneg : (0 : ℝ) ≤ (2 * (K : ℝ)) := by
      have : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
      nlinarith
    exact pow_le_pow_left₀ h2Knonneg h2Kle m
  have h2pow_le : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (3 * m) := by
    have h2one : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have hmn : m ≤ 3 * m := by
      -- 1*m ≤ 3*m
      simpa [Nat.one_mul] using (Nat.mul_le_mul_right m (by decide : (1 : ℕ) ≤ 3))
    exact pow_le_pow_right₀ h2one hmn
  have h2mul : (2 : ℝ) ^ m * ((K : ℝ) + 1) ^ m ≤ (2 : ℝ) ^ (3 * m) * ((K : ℝ) + 1) ^ m := by
    have hKn0 : 0 ≤ ((K : ℝ) + 1) ^ m := by
      have hk0 : 0 ≤ (K : ℝ) + 1 := by
        have hk0' : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
        linarith
      exact pow_nonneg hk0 m
    exact mul_le_mul_of_nonneg_right h2pow_le hKn0
  have h2Kfinal : (2 * (K : ℝ)) ^ m ≤ (2 : ℝ) ^ (3 * m) * ((K : ℝ) + 1) ^ m := by
    calc
      (2 * (K : ℝ)) ^ m ≤ (2 * ((K : ℝ) + 1)) ^ m := h2Kpow
      _ = (2 : ℝ) ^ m * ((K : ℝ) + 1) ^ m := by
        simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (2 : ℝ) ^ (3 * m) * ((K : ℝ) + 1) ^ m := h2mul
  -- rewrite B^m into factors
  have hspow : ((s : ℝ) ^ 2) ^ m = (s : ℝ) ^ (2 * m) := by
    simpa [pow_mul] using (pow_mul (s : ℝ) 2 m).symm
  have hBpow : B ^ m = (Real.exp 1 + 3) ^ m * (2 * (K : ℝ)) ^ m * (s : ℝ) ^ (2 * m) := by
    simp [B, mul_pow, mul_assoc, mul_left_comm, mul_comm, hspow]
  -- show c * B^m ≤ RHS using h2Kfinal
  have hB_le : c * B ^ m ≤ (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K : ℝ) + 1) ^ m * (s : ℝ) ^ (2 * m) := by
    rw [hBpow]
    -- multiply the inequality on (2*K)^m by the nonnegative factor c*(exp1+3)^m*(s)^(2*m)
    have tnonneg : 0 ≤ c * (Real.exp 1 + 3) ^ m * (s : ℝ) ^ (2 * m) := by
      have hexp : 0 ≤ (Real.exp 1 + 3) ^ m := by
        have hbase : 0 ≤ Real.exp 1 + 3 := by
          have hpos : 0 < Real.exp 1 := Real.exp_pos 1
          linarith
        exact pow_nonneg hbase m
      have hs0 : 0 ≤ (s : ℝ) ^ (2 * m) := by
        have : 0 ≤ (s : ℝ) := by exact_mod_cast (Nat.zero_le s)
        exact pow_nonneg this (2 * m)
      exact mul_nonneg (mul_nonneg hc hexp) hs0
    have := mul_le_mul_of_nonneg_left h2Kfinal tnonneg
    -- clean up the algebra
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  -- finish
  have hfinal : c * Real.rpow x q ≤ (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K : ℝ) + 1) ^ m * (s : ℝ) ^ (2 * m) :=
    le_trans hleft hB_le
  -- rewrite (↑K + 1) as ↑(K+1) if needed and close the goal
  simpa using hfinal


theorem X_ncard_add_one_le_Aconst (n : ℕ) (G : Set (FreeAbelianMonoid n)) (c q : ℝ)
  (hc : 0 ≤ c)
  (hG : ∀ r : ℕ, (G ∩ Ball r (A n)).ncard ≤ c * Real.rpow (Real.log (Real.exp 1 + r)) q)
  (K s : ℕ) (hK : 2 ≤ K) (hs : 2 ≤ s) :
  let m : ℕ := Nat.ceil |q|
  let Aconst : ℝ :=
    (2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m
  let r : ℕ := rKS K s
  let X : Set (FreeAbelianMonoid n) := (G ∩ Ball r (A n)) ∪ A n
  (X.ncard + 1 : ℝ) ≤ Aconst * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
  classical
  dsimp
  set m : ℕ := Nat.ceil |q| with hm
  set r : ℕ := rKS K s with hr
  set X : Set (FreeAbelianMonoid n) := (G ∩ Ball r (A n)) ∪ A n with hX
  set Aconst : ℝ :=
      (2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m with hA

  have hXnat : X.ncard + 1 ≤ (G ∩ Ball r (A n)).ncard + n + 1 := by
    have h' : X.ncard ≤ (G ∩ Ball r (A n)).ncard + (A n).ncard := by
      simpa [hX] using (Set.ncard_union_le (G ∩ Ball r (A n)) (A n))
    have h'' : X.ncard + 1 ≤ (G ∩ Ball r (A n)).ncard + (A n).ncard + 1 :=
      Nat.add_le_add_right h' 1
    simpa [A_ncard, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h''

  have hXreal : (X.ncard + 1 : ℝ) ≤ ((G ∩ Ball r (A n)).ncard : ℝ) + (n : ℝ) + 1 := by
    have : (X.ncard + 1 : ℝ) ≤ ((G ∩ Ball r (A n)).ncard + n + 1 : ℝ) := by
      exact_mod_cast hXnat
    simpa [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, add_left_comm, add_comm] using this

  have hGr : ((G ∩ Ball r (A n)).ncard : ℝ) ≤
      c * Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q := by
    simpa using (hG r)

  have hXreal' : (X.ncard + 1 : ℝ) ≤
      c * Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q + (n : ℝ) + 1 := by
    have htmp : ((G ∩ Ball r (A n)).ncard : ℝ) + (n : ℝ) + 1 ≤
        c * Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q + (n : ℝ) + 1 := by
      have := add_le_add_right hGr ((n : ℝ) + 1)
      simpa [add_assoc, add_left_comm, add_comm] using this
    exact le_trans hXreal htmp

  have hcr : c * Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q ≤
      (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
    have hcr0 := c_rpow_log_exp1_add_rKS_le c q hc K s hK hs
    have hm' : Nat.ceil |q| = m := hm.symm
    have hr' : (rKS K s : ℝ) = (r : ℝ) := by
      exact_mod_cast hr.symm
    simpa [hm', hr', m] using hcr0

  have hXreal'' : (X.ncard + 1 : ℝ) ≤
      (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)
        + (n : ℝ) + 1 := by
    have htmp : c * Real.rpow (Real.log (Real.exp 1 + (r : ℝ))) q + (n : ℝ) + 1 ≤
        (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)
          + (n : ℝ) + 1 := by
      have := add_le_add_right hcr ((n : ℝ) + 1)
      simpa [add_assoc, add_left_comm, add_comm] using this
    exact le_trans hXreal' htmp

  have hK1 : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le K))

  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hs)

  have hpowK : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ m := by
    simpa using (one_le_pow₀ hK1 (n := m))

  have hpows : (1 : ℝ) ≤ (s : ℝ) ^ (2 * m) := by
    simpa using (one_le_pow₀ hs1 (n := 2 * m))

  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    simpa using (one_le_pow₀ h2 (n := 2 * m))

  have hfac : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * m) * (((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)) := by
    have hmul1 : (1 : ℝ) ≤ (((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)) := by
      have h0K : (0 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ m := by
        exact pow_nonneg (by positivity) _
      have := mul_le_mul hpowK hpows (by linarith) h0K
      simpa [one_mul] using this
    have h0pow2 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
      exact pow_nonneg (by positivity) _
    have := mul_le_mul hpow2 hmul1 (by linarith) h0pow2
    simpa [one_mul, mul_assoc] using this

  have hn1_nonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    linarith

  have hn_bound : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
    have := mul_le_mul_of_nonneg_left hfac hn1_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm, one_mul] using this

  have hfinal : (X.ncard + 1 : ℝ) ≤
      Aconst * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
    have hXtmp : (X.ncard + 1 : ℝ) ≤
        (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)
          + ((n : ℝ) + 1) := by
      simpa [add_assoc, add_left_comm, add_comm] using hXreal''

    have hsum :
        (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)
          + ((n : ℝ) + 1)
        ≤
        (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)
          + (2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
      have := add_le_add_left hn_bound
        ((2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m))
      simpa [add_assoc, add_left_comm, add_comm] using this

    have hXtmp2 : (X.ncard + 1 : ℝ) ≤
        (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)
          + (2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) :=
      le_trans hXtmp hsum

    have hXtmp2' : (X.ncard + 1 : ℝ) ≤
        (2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m)
          + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
      -- only reorder the sum, no other simp
      have := hXtmp2
      -- rewrite using add_comm
      simpa [add_comm, add_left_comm, add_assoc] using this

    -- factor out common terms; work in the simp-normal form of casts
    have hrew :
        (2 : ℝ) ^ (2 * m) * (↑n + 1) * (↑K + 1) ^ m * (↑s) ^ (2 * m)
          + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * (↑K + 1) ^ m * (↑s) ^ (2 * m)
        =
        ((2 : ℝ) ^ (2 * m) * (↑n + 1) + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m)
          * (↑K + 1) ^ m * (↑s) ^ (2 * m) := by
      ring

    have : (X.ncard + 1 : ℝ) ≤
        ((2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m)
          * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
      -- convert hXtmp2' to the simp-normal form, then rewrite
      have hXtmp2'' : (X.ncard + 1 : ℝ) ≤
          (2 : ℝ) ^ (2 * m) * (↑n + 1) * (↑K + 1) ^ m * (↑s) ^ (2 * m)
            + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m * (↑K + 1) ^ m * (↑s) ^ (2 * m) := by
        simpa using hXtmp2'
      have hXtmp2''' : (X.ncard + 1 : ℝ) ≤
          ((2 : ℝ) ^ (2 * m) * (↑n + 1) + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m)
            * (↑K + 1) ^ m * (↑s) ^ (2 * m) := by
        simpa [hrew] using hXtmp2''
      -- go back to the original cast form
      simpa using hXtmp2'''

    simpa [hA] using this

  simpa [hX, hm, hr] using hfinal


theorem toList_map_singleton_sum {n : ℕ} (m : FreeAbelianMonoid n) :
  (m.toList.map (fun a : Fin n => ({a} : Multiset (Fin n)))).sum = m := by
  classical
  let f : Fin n → Multiset (Fin n) := fun a => ({a} : Multiset (Fin n))
  -- Turn the list sum into a multiset sum.
  rw [← Multiset.sum_coe (m.toList.map f)]
  -- Rewrite the coerced list as a mapped multiset.
  have hmap : ((m.toList.map f : List (Multiset (Fin n))) : Multiset (Multiset (Fin n))) =
      (m.toList : Multiset (Fin n)).map f := by
    simpa using (Multiset.map_coe f m.toList).symm
  -- Now simplify using `coe_toList` and `sum_map_singleton`.
  simpa [f, hmap] using (Multiset.sum_map_singleton (m.toList : Multiset (Fin n)))


theorem mem_Ball_A_iff_card_le {n r : ℕ} (m : FreeAbelianMonoid n) : m ∈ Ball r (A n) ↔ m.card ≤ r := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hl_len, hlA, hl_sum⟩
    have hcard_sum :
        ∀ l : List (FreeAbelianMonoid n),
          (∀ x, x ∈ l → x ∈ A n) → (l.sum).card = l.length := by
      intro l hlA
      induction l with
      | nil =>
          simp
      | cons a t ih =>
          have ha_mem : a ∈ A n := hlA a (by simp)
          rcases ha_mem with ⟨i, rfl⟩
          have htA : ∀ x, x ∈ t → x ∈ A n := by
            intro x hx
            exact hlA x (by simp [hx])
          simpa [List.sum_cons, Multiset.card_add, ih htA, Nat.succ_eq_add_one, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc]
    have hmcard : m.card = l.length := by
      have : (l.sum).card = l.length := hcard_sum l hlA
      simpa [hl_sum] using this
    simpa [hmcard] using hl_len
  · intro hmle
    have hm_in : m ∈ Ball m.card (A n) := by
      refine ⟨m.toList.map (fun a : Fin n => ({a} : Multiset (Fin n))), ?_, ?_, ?_⟩
      · simp
      · intro x hx
        rcases List.mem_map.1 hx with ⟨a, ha, rfl⟩
        exact ⟨a, rfl⟩
      · simpa using (toList_map_singleton_sum (n := n) m)
    exact (Ball_mono_radius (n := n) (R := m.card) (S := r) (X := A n) hmle) hm_in

theorem BallA_ncard_lower (n r : ℕ) (hn : 0 < n) : r + 1 ≤ (Ball r (A n)).ncard := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let f : Fin (r + 1) → FreeAbelianMonoid n := fun k => Multiset.replicate (k : ℕ) i0
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Multiset.card hab
    simpa [f, Multiset.card_replicate] using h
  have hsub : Set.range f ⊆ Ball r (A n) := by
    rintro m ⟨k, rfl⟩
    have hk : (k : ℕ) ≤ r := by
      exact Nat.lt_succ_iff.mp k.isLt
    have : (Multiset.replicate (k : ℕ) i0).card ≤ r := by
      simpa [Multiset.card_replicate] using hk
    exact (mem_Ball_A_iff_card_le (n := n) (r := r)
      (m := Multiset.replicate (k : ℕ) i0)).2 this
  have hcard : (Set.range f).ncard = r + 1 := by
    simpa [f, Nat.card_fin] using (Set.ncard_range_of_injective (f := f) hf)
  have hAfinite : (A n).Finite := by
    simpa [A] using (Set.finite_range (fun i : Fin n => ({i} : Multiset (Fin n))))
  have hBallfinite : (Ball r (A n)).Finite :=
    Ball_finite_of_finite (n := n) (R := r) (X := A n) hAfinite
  have hle : (Set.range f).ncard ≤ (Ball r (A n)).ncard := by
    exact Set.ncard_le_ncard hsub hBallfinite
  simpa [hcard] using hle

theorem Ball_restrict_generators {n r s : ℕ} (G : Set (FreeAbelianMonoid n)) : Ball r (A n) ⊆ Ball s (G ∪ A n) → Ball r (A n) ⊆ Ball s ((G ∩ Ball r (A n)) ∪ A n) := by
  intro h
  intro m hm
  rcases h hm with ⟨l, hl_len, hl_mem, hl_sum⟩
  refine ⟨l, hl_len, ?_, hl_sum⟩
  intro x hx
  have hxGA : x ∈ G ∪ A n := hl_mem x hx
  rcases hxGA with hxG | hxA
  · left
    refine ⟨hxG, ?_⟩
    have hmcard : m.card ≤ r := (mem_Ball_A_iff_card_le (n:=n) (r:=r) m).1 hm
    have hxleSum : x ≤ l.sum := by
      have hnonneg : ∀ y ∈ l, (0 : FreeAbelianMonoid n) ≤ y := by
        intro y hy
        simpa using (zero_le y)
      exact List.single_le_sum (l := l) hnonneg x hx
    have hxcardle : x.card ≤ (l.sum).card := Multiset.card_le_card hxleSum
    have hsumcard : (l.sum).card ≤ r := by
      simpa [hl_sum] using hmcard
    have hxcard : x.card ≤ r := le_trans hxcardle hsumcard
    exact (mem_Ball_A_iff_card_le (n:=n) (r:=r) x).2 hxcard
  · right
    exact hxA

theorem theorem_2_quasi_exponential_expansion (n : ℕ) (hn : 0 < n) (G : Set (FreeAbelianMonoid n)) (c q : ℝ) :
  (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) →
    (∃ (K : ℕ), ∀ (s : ℕ), s ≥ 2 → (K ≥ 0) ∧
      let r := 1 + Int.toNat (Int.floor (Real.exp (K * s * (Real.log s))))
      ¬ (Ball r (A n) ⊆ Ball s (G ∪ (A n)))) := by
  intro hG
  classical
  have hc : 0 ≤ c := by
    have h0 : ((G ∩ Ball 0 (A n)).ncard : ℝ) ≤ c := by
      simpa using (hG 0)
    have hnonneg : (0 : ℝ) ≤ ((G ∩ Ball 0 (A n)).ncard : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    exact le_trans hnonneg h0

  let m : ℕ := Nat.ceil |q|
  let Aconst : ℝ :=
    (2 : ℝ) ^ (2 * m) * ((n : ℝ) + 1) + (2 : ℝ) ^ (3 * m) * c * (Real.exp 1 + 3) ^ m
  let Acoef : ℝ := (2 : ℝ) ^ (2 * m) * Aconst

  have hAcoef : 0 ≤ Acoef := by
    positivity [hc]

  obtain ⟨K0, hK0⟩ := exists_K0_mul_pow_lt_two_pow Acoef hAcoef m

  let K : ℕ := max (2 * m + 2) K0

  refine ⟨K, ?_⟩
  intro s hs
  refine ⟨Nat.zero_le K, ?_⟩

  -- reduce the `let r := ...` in the statement to `rKS K s`
  simpa [rKS] using (show ¬ (Ball (rKS K s) (A n) ⊆ Ball s (G ∪ A n)) from by
    intro hsub0

    -- restrict generators
    have hsub : Ball (rKS K s) (A n) ⊆ Ball s ((G ∩ Ball (rKS K s) (A n)) ∪ A n) := by
      exact Ball_restrict_generators (n := n) (r := rKS K s) (s := s) (G := G) hsub0

    -- lower bound on ncard of Ball r(A n)
    have hlow : (rKS K s) + 1 ≤ (Ball (rKS K s) (A n)).ncard := by
      simpa using BallA_ncard_lower n (rKS K s) hn

    -- finiteness facts
    have hfinA : (A n).Finite := by
      simpa [A] using (Set.finite_range (fun i : Fin n => ({i} : Multiset (Fin n))))

    have hfinBall : (Ball (rKS K s) (A n)).Finite := by
      exact Ball_finite_of_finite (X := A n) hfinA

    have hfinG' : (G ∩ Ball (rKS K s) (A n)).Finite := by
      refine hfinBall.subset ?_
      intro x hx
      exact hx.2

    have hfinX : ((G ∩ Ball (rKS K s) (A n)) ∪ A n).Finite := by
      exact hfinG'.union hfinA

    have hfinBallTarget : (Ball s ((G ∩ Ball (rKS K s) (A n)) ∪ A n)).Finite := by
      exact Ball_finite_of_finite (X := (G ∩ Ball (rKS K s) (A n)) ∪ A n) hfinX

    -- monotonicity of ncard under subset
    have hncard_mono : (Ball (rKS K s) (A n)).ncard ≤ (Ball s ((G ∩ Ball (rKS K s) (A n)) ∪ A n)).ncard := by
      exact Set.ncard_le_ncard hsub hfinBallTarget

    -- upper bound on ncard of Ball s X
    have hupper : (Ball s ((G ∩ Ball (rKS K s) (A n)) ∪ A n)).ncard ≤ (((G ∩ Ball (rKS K s) (A n)) ∪ A n).ncard + 1) ^ s := by
      exact Ball_ncard_upper ((G ∩ Ball (rKS K s) (A n)) ∪ A n) hfinX

    have hsandwich : (rKS K s) + 1 ≤ (((G ∩ Ball (rKS K s) (A n)) ∪ A n).ncard + 1) ^ s := by
      exact le_trans hlow (le_trans hncard_mono hupper)

    -- set r and X for readability
    set r : ℕ := rKS K s
    set X : Set (FreeAbelianMonoid n) := (G ∩ Ball r (A n)) ∪ A n

    have hsandwich' : r + 1 ≤ (X.ncard + 1) ^ s := by
      simpa [r, X] using hsandwich

    -- cast to reals
    have hsandwichR : (r + 1 : ℝ) ≤ (X.ncard + 1 : ℝ) ^ s := by
      exact_mod_cast hsandwich'

    -- exp term is less than r (hence < r+1)
    have h_exp_lt_r : Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ)) < (r : ℝ) := by
      simpa [r] using exp_lt_rKS K s

    have h_exp_lt : Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ)) < (r + 1 : ℝ) := by
      have hrlt : (r : ℝ) < (r + 1 : ℝ) := by
        linarith
      exact lt_trans h_exp_lt_r hrlt

    have h_exp_lt2 : Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ)) < (X.ncard + 1 : ℝ) ^ s := by
      exact lt_of_lt_of_le h_exp_lt hsandwichR

    have hexp_pos : 0 < Real.exp ((K : ℝ) * (s : ℝ) * Real.log (s : ℝ)) := by
      exact Real.exp_pos _

    have hlog : (K : ℝ) * (s : ℝ) * Real.log (s : ℝ) < Real.log ((X.ncard + 1 : ℝ) ^ s) := by
      have := Real.log_lt_log hexp_pos h_exp_lt2
      simpa using this

    have hlog' : (K : ℝ) * (s : ℝ) * Real.log (s : ℝ) < (s : ℝ) * Real.log (X.ncard + 1 : ℝ) := by
      simpa [Real.log_pow] using hlog

    have hspos : (0 : ℝ) < (s : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hs)

    have hmul : (s : ℝ) * ((K : ℝ) * Real.log (s : ℝ)) < (s : ℝ) * Real.log (X.ncard + 1 : ℝ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hlog'

    have hlog'' : (K : ℝ) * Real.log (s : ℝ) < Real.log (X.ncard + 1 : ℝ) := by
      -- cancel the (nonnegative) factor `s`
      exact lt_of_mul_lt_mul_left hmul (le_of_lt hspos)

    have hsK_lt : (s : ℝ) ^ K < (X.ncard + 1 : ℝ) := by
      have hexp := (Real.exp_lt_exp).2 hlog''
      have hleft : Real.exp ((K : ℝ) * Real.log (s : ℝ)) = (s : ℝ) ^ K := by
        simpa [Real.exp_log hspos] using (Real.exp_nat_mul (Real.log (s : ℝ)) K)
      have hxpos : 0 < (X.ncard + 1 : ℝ) := by
        have : (0 : ℝ) ≤ (X.ncard : ℝ) := by
          exact_mod_cast (Nat.zero_le _)
        linarith
      have hright : Real.exp (Real.log (X.ncard + 1 : ℝ)) = (X.ncard + 1 : ℝ) := by
        simpa [Real.exp_log hxpos]
      simpa [hleft, hright] using hexp

    -- apply the provided bound on X.ncard
    have hK2 : 2 ≤ K := by
      have h2 : 2 ≤ 2 * m + 2 := by omega
      exact le_trans h2 (Nat.le_max_left _ _)

    have hs2 : 2 ≤ s := hs

    have hXupper : (X.ncard + 1 : ℝ) ≤ Aconst * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
      simpa [m, Aconst, r, X] using
        (X_ncard_add_one_le_Aconst n G c q hc hG K s hK2 hs2)

    have hsK_lt_upper : (s : ℝ) ^ K < Aconst * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) :=
      lt_of_lt_of_le hsK_lt hXupper

    -- rewrite s^K as s^(2*m) * s^(K-2*m)
    have h2m_le_K : 2 * m ≤ K := by
      have h2m : 2 * m ≤ 2 * m + 2 := by omega
      exact le_trans h2m (Nat.le_max_left _ _)

    let t : ℕ := K - 2 * m
    have hK_eq : K = 2 * m + t := by
      simpa [t] using (Nat.add_sub_of_le h2m_le_K).symm

    have hs2m_pos : 0 < (s : ℝ) ^ (2 * m) := by
      positivity

    have ht_lt : (s : ℝ) ^ t < Aconst * ((K + 1 : ℕ) : ℝ) ^ m := by
      -- cancel `s^(2*m)`
      have hsK_lt_upper' : (s : ℝ) ^ (2 * m) * (s : ℝ) ^ t < (s : ℝ) ^ (2 * m) * (Aconst * ((K + 1 : ℕ) : ℝ) ^ m) := by
        have : (s : ℝ) ^ (2 * m) * (s : ℝ) ^ t < Aconst * ((K + 1 : ℕ) : ℝ) ^ m * (s : ℝ) ^ (2 * m) := by
          have : (s : ℝ) ^ K = (s : ℝ) ^ (2 * m) * (s : ℝ) ^ t := by
            calc
              (s : ℝ) ^ K = (s : ℝ) ^ (2 * m + t) := by simpa [hK_eq]
              _ = (s : ℝ) ^ (2 * m) * (s : ℝ) ^ t := by
                simpa [pow_add, mul_assoc]
          simpa [this] using hsK_lt_upper
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      exact lt_of_mul_lt_mul_left hsK_lt_upper' (le_of_lt hs2m_pos)

    have h2_le_s_real : (2 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs2

    have h2t_le : (2 : ℝ) ^ t ≤ (s : ℝ) ^ t := by
      exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2_le_s_real t

    have h2t_lt : (2 : ℝ) ^ t < Aconst * ((K + 1 : ℕ) : ℝ) ^ m := by
      exact lt_of_le_of_lt h2t_le ht_lt

    -- multiply by 2^(2*m) to compare with hK0
    have h2K_lt : (2 : ℝ) ^ K < Acoef * ((K + 1 : ℕ) : ℝ) ^ m := by
      have h2K : (2 : ℝ) ^ K = (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ t := by
        calc
          (2 : ℝ) ^ K = (2 : ℝ) ^ (2 * m + t) := by simpa [hK_eq]
          _ = (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ t := by
            simpa [pow_add, mul_assoc]
      have h2m_pos : 0 < (2 : ℝ) ^ (2 * m) := by
        positivity
      have hmul : (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ t < (2 : ℝ) ^ (2 * m) * (Aconst * ((K + 1 : ℕ) : ℝ) ^ m) := by
        exact mul_lt_mul_of_pos_left h2t_lt h2m_pos
      have hR : (2 : ℝ) ^ (2 * m) * (Aconst * ((K + 1 : ℕ) : ℝ) ^ m) = Acoef * ((K + 1 : ℕ) : ℝ) ^ m := by
        simp [Acoef, mul_assoc, mul_left_comm, mul_comm]
      have hmul' : (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ t < Acoef * ((K + 1 : ℕ) : ℝ) ^ m := by
        -- rewrite the RHS of `hmul`
        exact hmul.trans_eq hR
      -- rewrite the LHS using `h2K`
      exact (lt_of_eq_of_lt h2K hmul')

    have hcontr : Acoef * ((K + 1 : ℕ) : ℝ) ^ m < (2 : ℝ) ^ K := by
      have hK_ge_K0 : K0 ≤ K := Nat.le_max_right (2 * m + 2) K0
      exact hK0 K hK_ge_K0

    exact lt_asymm h2K_lt hcontr
  )
