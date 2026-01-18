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

open scoped BigOperators
open FreeMonoid

def A (n : ℕ) : Set (FreeMonoid (Fin n)) :=
  Set.range (fun i : Fin n => FreeMonoid.of i)

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeMonoid (Fin n))) : Set (FreeMonoid (Fin n)) :=
  {m | ∃ l : List (FreeMonoid (Fin n)), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.prod = m}

theorem compositionAsSetEquiv_symm_length (r : ℕ) (hr : 1 ≤ r) (s : Finset (Fin (r - 1))) :
  ((compositionAsSetEquiv r).symm s).length = s.card + 1 := by
  classical
  -- shift map : j ↦ j+1 as an element of `Fin (r+1)`
  let f : Fin (r - 1) → Fin r.succ := fun j =>
    ⟨(j : ℕ) + 1, by
      have hj : (j : ℕ) < r - 1 := j.is_lt
      have hle : (j : ℕ) + 1 ≤ r := by
        -- `j+1 ≤ r-1 ≤ r`
        exact le_trans (Nat.succ_le_of_lt hj) (Nat.sub_le r 1)
      exact Nat.lt_succ_of_le hle⟩

  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have : (a : ℕ) + 1 = (b : ℕ) + 1 := by
      simpa [f] using congrArg Fin.val hab
    exact Nat.succ_injective this

  -- identify the boundary set
  have hbound :
      ((compositionAsSetEquiv r).symm s).boundaries =
        insert (0 : Fin r.succ) (insert (Fin.last r) (s.image f)) := by
    ext i
    constructor
    · intro hi
      have hi' :
          i = 0 ∨ i = Fin.last r ∨
            ∃ (j : Fin (r - 1)) (_hj : j ∈ s), (i : ℕ) = j + 1 := by
        simpa [compositionAsSetEquiv] using hi
      rcases hi' with h0 | hlast | hmid
      · simp [h0]
      · simp [hlast]
      · rcases hmid with ⟨j, hj, hij⟩
        have hfj : f j = i := by
          apply Fin.ext
          -- prove equality of values
          simpa [f, hij]
        have himg : i ∈ s.image f := Finset.mem_image.2 ⟨j, hj, hfj⟩
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem himg)
    · intro hi
      have hi' : i = 0 ∨ i = Fin.last r ∨ i ∈ s.image f := by
        simpa [Finset.mem_insert, or_left_comm, or_assoc, or_comm] using hi
      rcases hi' with h0 | hlast | himg
      · simpa [compositionAsSetEquiv, h0]
      · simpa [compositionAsSetEquiv, hlast]
      · rcases Finset.mem_image.1 himg with ⟨j, hj, rfl⟩
        -- show membership in boundaries via the third alternative
        have :
            (f j = (0 : Fin r.succ)) ∨ f j = Fin.last r ∨
              ∃ (j' : Fin (r - 1)) (_hj' : j' ∈ s), (f j : ℕ) = j' + 1 := by
          refine Or.inr (Or.inr ?_)
          refine ⟨j, hj, ?_⟩
          simp [f]
        simpa [compositionAsSetEquiv] using this

  -- disjointness: 0 and last are not in the shifted image
  have hzero_not_mem_img : (0 : Fin r.succ) ∉ s.image f := by
    intro h
    rcases Finset.mem_image.1 h with ⟨j, _hj, hj0⟩
    have : (f j : ℕ) = 0 := by
      simpa using congrArg Fin.val hj0
    simpa [f] using this

  have hlast_not_mem_img : (Fin.last r : Fin r.succ) ∉ s.image f := by
    intro h
    rcases Finset.mem_image.1 h with ⟨j, _hj, hjlast⟩
    have hval : (j : ℕ) + 1 = r := by
      have := congrArg Fin.val hjlast
      -- `Fin.last r` has value `r`
      simpa [f] using this
    have hjlt : (j : ℕ) < r - 1 := j.is_lt
    have hle : (j : ℕ) + 1 ≤ r - 1 := Nat.succ_le_of_lt hjlt
    have : r ≤ r - 1 := by
      simpa [hval] using hle
    have hrpos : 0 < r := lt_of_lt_of_le (Nat.zero_lt_succ 0) hr
    have hlt : r - 1 < r := Nat.sub_lt hrpos (by decide : 0 < 1)
    exact (not_le_of_gt hlt) this

  have hlast_ne_zero : (Fin.last r : Fin r.succ) ≠ 0 := by
    intro h
    have : r = 0 := by
      simpa using congrArg Fin.val h
    have hrpos : 0 < r := lt_of_lt_of_le (Nat.zero_lt_succ 0) hr
    exact (Nat.ne_of_gt hrpos) this

  have hcard_img : (s.image f).card = s.card := by
    exact Finset.card_image_of_injective s hf

  have hcard_boundaries : ((compositionAsSetEquiv r).symm s).boundaries.card = s.card + 2 := by
    rw [hbound]
    have h1 : (insert (Fin.last r) (s.image f)).card = (s.image f).card + 1 := by
      exact Finset.card_insert_of_not_mem hlast_not_mem_img
    have h0not : (0 : Fin r.succ) ∉ insert (Fin.last r) (s.image f) := by
      intro h0
      rcases Finset.mem_insert.1 h0 with h0last | h0img
      · exact hlast_ne_zero h0last.symm
      · exact hzero_not_mem_img h0img
    have h2 : (insert (0 : Fin r.succ) (insert (Fin.last r) (s.image f))).card =
        (insert (Fin.last r) (s.image f)).card + 1 := by
      exact Finset.card_insert_of_not_mem h0not
    calc
      (insert (0 : Fin r.succ) (insert (Fin.last r) (s.image f))).card
          = (insert (Fin.last r) (s.image f)).card + 1 := h2
      _ = (s.image f).card + 1 + 1 := by
        simp [h1, Nat.add_assoc]
      _ = s.card + 2 := by
        rw [hcard_img]

  -- finish: length = card(boundaries) - 1
  -- and card(boundaries) = s.card + 2
  simp [CompositionAsSet.length, hcard_boundaries, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]


theorem composition_card_len_succ (r j : ℕ) (hr : 1 ≤ r) : Fintype.card {c : Composition r // c.length = j + 1} = (r - 1).choose j := by
  classical

  -- Step 1: transfer to `CompositionAsSet` using `compositionEquiv`.
  have hcard₁ :
      Fintype.card {c : Composition r // c.length = j + 1} =
        Fintype.card {c : CompositionAsSet r // c.length = j + 1} := by
    simpa using
      (Fintype.card_congr
        ((compositionEquiv r).subtypeEquiv (by
          intro c
          simp [compositionEquiv])))

  -- Step 2: transfer to finsets of `Fin (r-1)` using `compositionAsSetEquiv`.
  have hcard₂' :
      Fintype.card {s : Finset (Fin (r - 1)) // s.card = j} =
        Fintype.card {c : CompositionAsSet r // c.length = j + 1} := by
    refine
      Fintype.card_congr
        ((compositionAsSetEquiv r).symm.subtypeEquiv (by
          intro s
          have hlen : ((compositionAsSetEquiv r).symm s).length = s.card + 1 :=
            compositionAsSetEquiv_symm_length r hr s
          constructor
          · intro hs
            calc
              ((compositionAsSetEquiv r).symm s).length = s.card + 1 := hlen
              _ = j + 1 := by simpa [hs]
          · intro hslen
            have : s.card + 1 = j + 1 := by
              simpa [hlen] using hslen
            exact Nat.add_right_cancel this))

  have hcard₂ :
      Fintype.card {c : CompositionAsSet r // c.length = j + 1} =
        Fintype.card {s : Finset (Fin (r - 1)) // s.card = j} :=
    hcard₂'.symm

  -- Step 3: count finsets of cardinality `j`.
  calc
    Fintype.card {c : Composition r // c.length = j + 1}
        = Fintype.card {c : CompositionAsSet r // c.length = j + 1} := hcard₁
    _ = Fintype.card {s : Finset (Fin (r - 1)) // s.card = j} := hcard₂
    _ = (r - 1).choose j := by
      simpa using (Fintype.card_finset_len (α := Fin (r - 1)) j)


theorem freeMonoid_length_list_prod (n : ℕ) (l : List (FreeMonoid (Fin n))) : (l.prod).length = (l.map FreeMonoid.length).sum := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp [FreeMonoid.length_mul, ih]

theorem freeMonoid_prod_filter_length_ne_zero (n : ℕ) (l : List (FreeMonoid (Fin n))) : (l.filter (fun x => x.length ≠ 0)).prod = l.prod := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      have ih' : (l.filter (fun x => !decide (x.length = 0))).prod = l.prod := by
        simpa using ih
      by_cases h0 : a.length = 0
      · have ha : a = 1 := (FreeMonoid.length_eq_zero).1 h0
        simp [h0, ha, ih']
      · have ha : a.length ≠ 0 := h0
        simp [ha, ih']


noncomputable def logDensityD (n c : ℕ) : ℕ :=
  Int.toNat
    (max 2
      (Int.ceil (2 * (Real.log (2 * (Real.exp 1) * (n + c))) / (Real.log n))))

theorem logDensityD_ge_two (n c : ℕ) : 2 ≤ logDensityD n c := by
  unfold logDensityD
  set z : Int :=
    max 2
      (Int.ceil (2 * (Real.log (2 * (Real.exp 1) * (n + c))) / (Real.log n))) with hz
  have hz2 : (2 : Int) ≤ z := by
    simpa [hz] using
      (le_max_left (2 : Int)
        (Int.ceil (2 * (Real.log (2 * (Real.exp 1) * (n + c))) / (Real.log n))))
  by_contra h
  have hlt : z.toNat < 2 := by
    exact lt_of_not_ge h
  have hzlt : z < 2 := (Int.toNat_lt_of_ne_zero (m := z) (by decide)).1 hlt
  exact (not_lt_of_ge hz2) hzlt

theorem logDensityD_pow_ge_square (n c : ℕ) (hn : 2 ≤ n) :
  (2 * (Real.exp 1) * (n + c) : ℝ) ^ 2 ≤ (n : ℝ) ^ (logDensityD n c) := by
  classical
  set x : ℝ := (2 * Real.exp 1 * (n + c) : ℝ) with hx
  set y : ℝ := 2 * Real.log x / Real.log n with hy
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by
      exact lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
    exact_mod_cast this
  have hn_one_lt : (1 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := by
      exact lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn
    exact_mod_cast this
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_one_lt
  have hlogn_ne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlogn_pos
  have hn_one_le : (1 : ℝ) ≤ (n : ℝ) := le_of_lt hn_one_lt
  have hxpos : 0 < x := by
    have hnc_pos : (0 : ℝ) < (n + c : ℝ) := by
      have : (0 : ℕ) < n + c := Nat.add_pos_left (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn) c
      exact_mod_cast this
    have h2 : (0 : ℝ) < 2 := by norm_num
    have hexp : (0 : ℝ) < Real.exp 1 := by simpa using (Real.exp_pos (1 : ℝ))
    simpa [hx, mul_assoc, mul_left_comm, mul_comm] using (mul_pos (mul_pos h2 hexp) hnc_pos)
  have hy_le : y ≤ (logDensityD n c : ℝ) := by
    have hy_le_z : y ≤ ((max 2 (Int.ceil y) : ℤ) : ℝ) := by
      have h1 : y ≤ (Int.ceil y : ℝ) := by
        simpa using (Int.le_ceil (a := y))
      have h2 : (Int.ceil y : ℝ) ≤ ((max 2 (Int.ceil y) : ℤ) : ℝ) := by
        have : Int.ceil y ≤ max 2 (Int.ceil y) := by
          simpa using (le_max_right 2 (Int.ceil y))
        exact_mod_cast this
      exact le_trans h1 h2
    have hz_nonneg : (0 : ℤ) ≤ max 2 (Int.ceil y) := by
      have : (0 : ℤ) ≤ 2 := by decide
      have h2 : (2 : ℤ) ≤ max 2 (Int.ceil y) := by
        simpa using (le_max_left 2 (Int.ceil y))
      exact le_trans this h2
    have hz_toNat : (Int.toNat (max 2 (Int.ceil y)) : ℤ) = max 2 (Int.ceil y) := by
      exact Int.toNat_of_nonneg hz_nonneg
    have hz_cast : (Int.toNat (max 2 (Int.ceil y)) : ℝ) = ((max 2 (Int.ceil y) : ℤ) : ℝ) := by
      exact_mod_cast hz_toNat
    have : y ≤ (Int.toNat (max 2 (Int.ceil y)) : ℝ) := by
      simpa [hz_cast] using hy_le_z
    simpa [logDensityD, hy, hx] using this
  have hxpow : (n : ℝ) ^ y = x ^ (2 : ℕ) := by
    have hnpos : 0 < (n : ℝ) := hn_pos
    have hcancel : Real.log (n : ℝ) * y = 2 * Real.log x := by
      calc
        Real.log (n : ℝ) * y = Real.log (n : ℝ) * (2 * Real.log x / Real.log (n : ℝ)) := by
          simpa [hy]
        _ = (Real.log (n : ℝ) * (2 * Real.log x)) / Real.log (n : ℝ) := by
          simp [mul_div_assoc]
        _ = 2 * Real.log x := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_div_cancel_left₀ (2 * Real.log x) hlogn_ne)
    calc
      (n : ℝ) ^ y = Real.exp (Real.log (n : ℝ) * y) := by
        simpa using (Real.rpow_def_of_pos hnpos y)
      _ = Real.exp (2 * Real.log x) := by
        simp [hcancel]
      _ = x ^ (2 : ℕ) := by
        have : Real.exp (2 * Real.log x) = Real.exp (Real.log x) ^ (2 : ℕ) := by
          simpa using (Real.exp_nat_mul (Real.log x) 2)
        simpa [this, Real.exp_log hxpos]
  have hmono : (n : ℝ) ^ y ≤ (n : ℝ) ^ ((logDensityD n c : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn_one_le hy_le
  have hmono' : (n : ℝ) ^ y ≤ (n : ℝ) ^ (logDensityD n c) := by
    simpa [Real.rpow_natCast] using hmono
  -- final
  --
  have hxpow' : x ^ (2 : ℕ) = (n : ℝ) ^ y := hxpow.symm
  have : x ^ (2 : ℕ) ≤ (n : ℝ) ^ (logDensityD n c) := by
    exact le_trans (le_of_eq hxpow') hmono'
  simpa [hx, pow_two] using this


theorem mem_Ball_A (n : ℕ) (w : FreeMonoid (Fin n)) : w ∈ Ball w.length (A n) := by
  classical
  refine ⟨w.toList.map (fun a => FreeMonoid.of a), ?_, ?_, ?_⟩
  · -- length bound
    simpa [FreeMonoid.length] using (le_of_eq (by simp))
  · -- every element lies in A n
    intro x hx
    rcases List.mem_map.1 hx with ⟨a, ha, rfl⟩
    exact ⟨a, rfl⟩
  · -- product equals w
    apply FreeMonoid.toList.injective
    -- reduce to a statement about lists
    simp [FreeMonoid.toList_prod, FreeMonoid.toList_of]
    -- now prove flattening singletons gives back the original list
    induction w.toList with
    | nil => simp
    | cons a t ih => simp [ih]


theorem mem_filter_length_ne_zero (n : ℕ) (l : List (FreeMonoid (Fin n))) (x : FreeMonoid (Fin n)) :
  x ∈ l.filter (fun y => y.length ≠ 0) → x.length ≠ 0 := by
  intro hx
  have hx' := List.mem_filter.1 hx
  have hdec : decide (x.length ≠ 0) = true := hx'.2
  exact (Bool.decide_iff (p := x.length ≠ 0)).1 hdec


theorem mem_len_inter_ball_exists_comp (n : ℕ) (X : Set (FreeMonoid (Fin n))) :
  ∀ {r s : ℕ} {w : FreeMonoid (Fin n)},
    1 ≤ r → w.length = r → w ∈ Ball s X →
    ∃ comp : Composition r, comp.length ≤ s ∧
      ∃ f : Fin comp.length → FreeMonoid (Fin n),
        (∀ i, f i ∈ X ∧ (f i).length = comp.blocksFun i) ∧
        (List.ofFn f).prod = w := by
  classical
  intro r s w hrpos hwlen hwBall
  rcases hwBall with ⟨l, hl_len, hl_mem, hl_prod⟩
  let l' : List (FreeMonoid (Fin n)) := l.filter (fun x => x.length ≠ 0)
  have hl'prod : l'.prod = w := by
    dsimp [l']
    calc
      (l.filter (fun x => x.length ≠ 0)).prod = l.prod := freeMonoid_prod_filter_length_ne_zero n l
      _ = w := hl_prod
  have hl'len : l'.length ≤ s := by
    have hle : l'.length ≤ l.length := by
      dsimp [l']
      simpa using
        (List.length_filter_le (l := l)
          (p := fun x : FreeMonoid (Fin n) => x.length ≠ 0))
    exact le_trans hle hl_len
  have hsum : (l'.map FreeMonoid.length).sum = r := by
    have hlenprod : (l'.prod).length = (l'.map FreeMonoid.length).sum :=
      freeMonoid_length_list_prod n l'
    have hlen : w.length = (l'.map FreeMonoid.length).sum := by
      simpa [hl'prod] using hlenprod
    have : (l'.map FreeMonoid.length).sum = w.length := by
      simpa using hlen.symm
    simpa [hwlen] using this
  let blocks : List ℕ := l'.map FreeMonoid.length
  have hblocks_pos : ∀ {i : ℕ}, i ∈ blocks → 0 < i := by
    intro i hi
    have hi' : i ∈ l'.map FreeMonoid.length := by
      simpa [blocks] using hi
    rcases List.mem_map.1 hi' with ⟨x, hx_mem, rfl⟩
    have hx_mem_filter : x ∈ l.filter (fun y => y.length ≠ 0) := by
      simpa [l'] using hx_mem
    have hx_ne : x.length ≠ 0 := mem_filter_length_ne_zero n l x hx_mem_filter
    exact Nat.pos_of_ne_zero hx_ne
  let comp : Composition r :=
    ⟨blocks, by
      intro i hi
      exact hblocks_pos hi,
      by
        simpa [blocks] using hsum⟩
  have hlen_comp : comp.length = l'.length := by
    simp [Composition.length, comp, blocks]
  have hcomp_len : comp.length ≤ s := by
    simpa [hlen_comp] using hl'len
  refine ⟨comp, hcomp_len, ?_⟩
  let f : Fin comp.length → FreeMonoid (Fin n) := fun i => l'.get (Fin.cast hlen_comp i)
  refine ⟨f, ?_, ?_⟩
  · intro i
    constructor
    · have hi_mem_l' : f i ∈ l' := by
        have : l'.get (Fin.cast hlen_comp i) ∈ l' := List.get_mem _ _
        simpa [f] using this
      have hi_mem_filter : f i ∈ l.filter (fun x => x.length ≠ 0) := by
        simpa [l'] using hi_mem_l'
      have hi_mem_l : f i ∈ l := List.mem_of_mem_filter hi_mem_filter
      exact hl_mem (f i) hi_mem_l
    · -- length matches the corresponding block
      have hget : blocks.get i = (l'.get (Fin.cast hlen_comp i)).length := by
        simpa [blocks] using (List.get_map FreeMonoid.length l' i)
      simpa [f, Composition.blocksFun, comp] using hget.symm
  · have hofFn : List.ofFn f = l' := by
      have hcongr :
          List.ofFn (fun i : Fin comp.length => l'.get (Fin.cast hlen_comp i)) =
            List.ofFn (l'.get) :=
        (List.ofFn_congr (h := hlen_comp.symm) (f := l'.get)).symm
      have := hcongr.trans (List.ofFn_get l')
      simpa [f] using this
    calc
      (List.ofFn f).prod = l'.prod := by simpa [hofFn]
      _ = w := hl'prod


theorem ncard_generators_len_le (n c : ℕ)
  (G : Set (FreeMonoid (Fin n)))
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c)) :
  ∀ l : ℕ, l ≥ 1 → Set.ncard { x ∈ (G ∪ (A n)) | x.length = l } ≤ n + c := by
  classical
  intro l hl1
  cases l with
  | zero =>
      cases (Nat.not_succ_le_zero 0 hl1)
  | succ l =>
      cases l with
      | zero =>
          -- l = 1
          have hsub : { x ∈ (G ∪ (A n)) | x.length = 1 } ⊆ A n := by
            intro x hx
            rcases (FreeMonoid.length_eq_one).1 hx.2 with ⟨i, rfl⟩
            exact ⟨i, by rfl⟩
          have hAfinite : (A n).Finite := by
            simpa [A] using
              (Set.finite_range (fun i : Fin n => ([i] : FreeMonoid (Fin n))))
          have hs_le_A :
              Set.ncard { x ∈ (G ∪ (A n)) | x.length = 1 } ≤ Set.ncard (A n) := by
            exact Set.ncard_le_ncard hsub hAfinite
          have hA_le_n : Set.ncard (A n) ≤ n := by
            -- A n is the range of `FreeMonoid.of`
            have hcard : Set.ncard (Set.range (FreeMonoid.of : Fin n → FreeMonoid (Fin n))) = n := by
              simpa [Nat.card_fin] using
                (Set.ncard_range_of_injective (f := (FreeMonoid.of : Fin n → FreeMonoid (Fin n)))
                  (FreeMonoid.of_injective))
            have hAeq : A n = Set.range (FreeMonoid.of : Fin n → FreeMonoid (Fin n)) := by
              ext x
              constructor
              · rintro ⟨i, rfl⟩
                exact ⟨i, rfl⟩
              · rintro ⟨i, rfl⟩
                exact ⟨i, rfl⟩
            -- use the equality
            simpa [hAeq] using le_of_eq hcard
          have hs_le_n : Set.ncard { x ∈ (G ∪ (A n)) | x.length = 1 } ≤ n :=
            le_trans hs_le_A hA_le_n
          exact le_trans hs_le_n (Nat.le_add_right n c)
      | succ l =>
          -- l ≥ 2
          have hl2 : 2 ≤ Nat.succ (Nat.succ l) := by
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le l))
          have hset :
              { x ∈ (G ∪ (A n)) | x.length = Nat.succ (Nat.succ l) } =
                { x ∈ G | x.length = Nat.succ (Nat.succ l) } := by
            ext x
            constructor
            · intro hx
              rcases hx with ⟨hxU, hxL⟩
              rcases hxU with hxG | hxA
              · exact ⟨hxG, hxL⟩
              ·
                have hxA1 : x.length = 1 := by
                  rcases hxA with ⟨i, rfl⟩
                  exact FreeMonoid.length_of i
                have hEq : Nat.succ (Nat.succ l) = 1 := by
                  have hxA1' := hxA1
                  rw [hxL] at hxA1'
                  exact hxA1'
                have hEq' : Nat.succ l = 0 :=
                  Nat.succ_injective (by simpa using hEq)
                exact False.elim (Nat.succ_ne_zero l hEq')
            · intro hx
              exact ⟨Or.inl hx.1, hx.2⟩
          have hs_le_c :
              Set.ncard { x ∈ (G ∪ (A n)) | x.length = Nat.succ (Nat.succ l) } ≤ c := by
            rw [hset]
            exact hG (Nat.succ (Nat.succ l)) hl2
          exact le_trans hs_le_c (Nat.le_add_left c n)


theorem ncard_wordsOfComp_le_pow (n : ℕ) (X : Set (FreeMonoid (Fin n))) (N : ℕ)
  (hX : ∀ l : ℕ, l ≥ 1 → Set.ncard { x ∈ X | x.length = l } ≤ N) :
  ∀ (r : ℕ) (comp : Composition r),
    Set.ncard
        (Set.range
          (fun f : (∀ i : Fin comp.length,
              {x : FreeMonoid (Fin n) // x ∈ X ∧ x.length = comp.blocksFun i}) =>
            (List.ofFn (fun i => (f i).1)).prod))
      ≤ N ^ comp.length := by
  intro r comp
  classical
  -- Types of blocks of the composition.
  let β : Fin comp.length → Type := fun i =>
    {x : FreeMonoid (Fin n) // x ∈ X ∧ x.length = comp.blocksFun i}
  -- Multiply the chosen blocks.
  let g : (∀ i : Fin comp.length, β i) → FreeMonoid (Fin n) := fun f =>
    (List.ofFn (fun i => (f i).1)).prod

  -- Finiteness: each block type is finite (lists of fixed length over a finite alphabet).
  haveI hβfinite : ∀ i : Fin comp.length, Finite (β i) := by
    intro i
    -- First, words of a fixed length form a finite set.
    have hlen : ({x : FreeMonoid (Fin n) | x.length = comp.blocksFun i}).Finite := by
      -- `FreeMonoid (Fin n)` is defeq `List (Fin n)` and `Fin n` is finite.
      simpa [FreeMonoid.length] using
        (List.finite_length_eq (α := Fin n) (comp.blocksFun i))
    -- Hence the subtype of words of that length is a finite type.
    haveI : Finite {x : FreeMonoid (Fin n) // x.length = comp.blocksFun i} := by
      simpa using hlen.to_subtype
    -- Our `β i` injects into the length-subtype.
    refine
      Finite.of_injective
        (fun x : β i =>
          (⟨x.1, x.2.2⟩ : {x : FreeMonoid (Fin n) // x.length = comp.blocksFun i}))
        (by
          intro x y h
          apply Subtype.ext
          exact
            congrArg
              (fun z : {x : FreeMonoid (Fin n) // x.length = comp.blocksFun i} => z.1)
              h)

  -- Therefore the whole product type is finite.
  haveI : Finite (∀ i : Fin comp.length, β i) := by infer_instance

  -- Step 1: range bound by cardinality of the domain.
  have h₁ : Set.ncard (Set.range g) ≤ Nat.card (∀ i : Fin comp.length, β i) := by
    have huniv : (Set.univ : Set (∀ i : Fin comp.length, β i)).Finite := by
      simpa using (Set.finite_univ : (Set.univ : Set (∀ i : Fin comp.length, β i)).Finite)
    -- Use `ncard_image_le` on `univ`.
    have hle :
        Set.ncard (g '' (Set.univ : Set (∀ i : Fin comp.length, β i))) ≤
          Set.ncard (Set.univ : Set (∀ i : Fin comp.length, β i)) := by
      simpa using
        (Set.ncard_image_le (f := g) (s := (Set.univ : Set (∀ i : Fin comp.length, β i))) huniv)
    simpa [Set.image_univ, Set.ncard_univ] using hle

  -- Step 2: compute the cardinality of the dependent function type.
  have h₂ : Nat.card (∀ i : Fin comp.length, β i) = ∏ i : Fin comp.length, Nat.card (β i) := by
    simpa using (Nat.card_pi (β := β))

  -- Step 3: bound each factor by `N` and use a product estimate.
  have h₃ : (∏ i : Fin comp.length, Nat.card (β i)) ≤ N ^ comp.length := by
    simpa using
      (Finset.prod_le_pow_card (s := (Finset.univ : Finset (Fin comp.length)))
        (f := fun i => Nat.card (β i)) (n := N) (by
          intro i hi
          have hi1 : comp.blocksFun i ≥ 1 := by
            simpa using (comp.one_le_blocksFun i)
          -- bound the number of options for the `i`-th block using `hX`.
          simpa [β] using (hX (comp.blocksFun i) hi1)))

  have hmain : Set.ncard (Set.range g) ≤ N ^ comp.length := by
    calc
      Set.ncard (Set.range g) ≤ Nat.card (∀ i : Fin comp.length, β i) := h₁
      _ = ∏ i : Fin comp.length, Nat.card (β i) := h₂
      _ ≤ N ^ comp.length := h₃

  simpa [g, β] using hmain

theorem ncard_len_inter_ball_le (n : ℕ)
  (G : Set (FreeMonoid (Fin n)))
  (c : ℕ)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c)) :
  ∀ (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Set.ncard ({w : FreeMonoid (Fin n) | w.length = r} ∩ Ball s (G ∪ (A n)))
      ≤ (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := by
  classical
  intro r s hr hs
  let X : Set (FreeMonoid (Fin n)) := G ∪ A n
  have hX : ∀ l : ℕ, l ≥ 1 → Set.ncard { x ∈ X | x.length = l } ≤ n + c := by
    simpa [X] using (ncard_generators_len_le n c G hG)

  set S : Set (FreeMonoid (Fin n)) := {w : FreeMonoid (Fin n) | w.length = r} ∩ Ball s X

  -- index compositions by their length-1 : Fin s
  let C : Fin s → Type := fun j => {comp : Composition r // comp.length = (j : ℕ) + 1}
  let ι : Type := Sigma C

  -- words coming from a given composition
  let Words : ι → Set (FreeMonoid (Fin n)) := fun p =>
    Set.range
      (fun f : (∀ i : Fin (p.2.1.length),
          {x : FreeMonoid (Fin n) // x ∈ X ∧ x.length = p.2.1.blocksFun i}) =>
        (List.ofFn (fun i => (f i).1)).prod)

  -- Step 2: cover S by the union over compositions
  have hsubset : S ⊆ ⋃ p : ι, Words p := by
    intro w hw
    rcases hw with ⟨hwlen, hwball⟩
    rcases mem_len_inter_ball_exists_comp n X (r := r) (s := s) (w := w) hr hwlen hwball with
      ⟨comp, hcomp_le, f, hf, hwprod⟩
    have hcomp_pos : 0 < comp.length := by
      have : 0 < r := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hr
      exact comp.length_pos_of_pos this
    have hcomp_pos' : 1 ≤ comp.length := Nat.succ_le_of_lt hcomp_pos
    let jNat : ℕ := comp.length - 1
    have hjNat_succ_le : Nat.succ jNat ≤ s := by
      have : jNat + 1 = comp.length := by
        dsimp [jNat]
        simpa [Nat.add_comm] using (Nat.sub_add_cancel hcomp_pos')
      have : jNat + 1 ≤ s := by simpa [this] using hcomp_le
      simpa [Nat.succ_eq_add_one] using this
    have hjNat_lt : jNat < s := Nat.lt_of_succ_le hjNat_succ_le
    let j : Fin s := ⟨jNat, hjNat_lt⟩
    have hcomp_len_eq : comp.length = (j : ℕ) + 1 := by
      have : comp.length = jNat + 1 := by
        dsimp [jNat]
        simpa using (Nat.sub_add_cancel hcomp_pos').symm
      simpa [j, Nat.add_comm] using this
    let comp' : C j := ⟨comp, hcomp_len_eq⟩

    let f' : ∀ i : Fin comp.length,
        {x : FreeMonoid (Fin n) // x ∈ X ∧ x.length = comp.blocksFun i} :=
      fun i => ⟨f i, (hf i).1, (hf i).2⟩
    have hwprod' : (List.ofFn (fun i => (f' i).1)).prod = w := by
      simpa [f'] using hwprod

    refine Set.mem_iUnion.2 ?_
    refine ⟨⟨j, comp'⟩, ?_⟩
    refine ⟨f', ?_⟩
    simpa [Words, hwprod']

  -- the slice of words of length r is finite
  have hSliceFinite : ({w : FreeMonoid (Fin n) | w.length = r} : Set (FreeMonoid (Fin n))).Finite := by
    simpa [FreeMonoid.length] using (List.finite_length_eq (α := Fin n) r)

  -- every word produced from a composition of r has length r
  have hWords_len : ∀ p : ι, Words p ⊆ {w : FreeMonoid (Fin n) | w.length = r} := by
    intro p w hw
    rcases hw with ⟨f, rfl⟩
    have hlen0 : ((List.ofFn (fun i : Fin p.2.1.length => (f i).1)).prod).length =
        ((List.ofFn (fun i : Fin p.2.1.length => (f i).1)).map FreeMonoid.length).sum := by
      simpa using (freeMonoid_length_list_prod n (List.ofFn (fun i : Fin p.2.1.length => (f i).1)))
    have hlen1 :
        ((List.ofFn (fun i : Fin p.2.1.length => (f i).1)).map FreeMonoid.length).sum =
          (∑ i : Fin p.2.1.length, ((f i).1).length) := by
      simpa [List.map_ofFn] using
        (List.sum_ofFn (f := fun i : Fin p.2.1.length => ((f i).1).length))
    have hlen2 : (∑ i : Fin p.2.1.length, ((f i).1).length) =
          (∑ i : Fin p.2.1.length, p.2.1.blocksFun i) := by
      have hfun : (fun i : Fin p.2.1.length => ((f i).1).length) = fun i => p.2.1.blocksFun i := by
        funext i
        exact (f i).2.2
      simpa [hfun] using (Fintype.sum_congr hfun)
    have hlen3 : (∑ i : Fin p.2.1.length, p.2.1.blocksFun i) = r := by
      simpa using (p.2.1.sum_blocksFun)
    have : ((List.ofFn (fun i : Fin p.2.1.length => (f i).1)).prod).length = r := by
      calc
        ((List.ofFn (fun i : Fin p.2.1.length => (f i).1)).prod).length
            = ((List.ofFn (fun i : Fin p.2.1.length => (f i).1)).map FreeMonoid.length).sum := hlen0
        _ = (∑ i : Fin p.2.1.length, ((f i).1).length) := hlen1
        _ = (∑ i : Fin p.2.1.length, p.2.1.blocksFun i) := hlen2
        _ = r := hlen3
    exact this

  have hUnionFinite : (⋃ p : ι, Words p).Finite := by
    refine hSliceFinite.subset ?_
    intro w hw
    rcases Set.mem_iUnion.1 hw with ⟨p, hp⟩
    exact hWords_len p hp

  have hS_le_union : S.ncard ≤ (⋃ p : ι, Words p).ncard :=
    Set.ncard_le_ncard hsubset hUnionFinite
  have hUnion_le_sum : (⋃ p : ι, Words p).ncard ≤ ∑ p : ι, (Words p).ncard :=
    Set.ncard_iUnion_le_of_fintype Words

  -- bound each Words p by (n+c)^s
  have hWords_bound : ∀ p : ι, (Words p).ncard ≤ (n + c) ^ s := by
    intro p
    have hcomp : (Words p).ncard ≤ (n + c) ^ p.2.1.length := by
      simpa [Words] using (ncard_wordsOfComp_le_pow n X (n + c) hX r p.2.1)
    have hlen_le : p.2.1.length ≤ s := by
      rcases p with ⟨j, comp⟩
      have hjlt : (j : ℕ) < s := j.2
      have hlen : comp.1.length = (j : ℕ) + 1 := comp.2
      have : (j : ℕ) + 1 ≤ s := Nat.succ_le_of_lt hjlt
      simpa [hlen] using this
    by_cases hbase : n + c = 0
    · have hspos : 0 < s := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hs
      have hrpos : 0 < r := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hr
      have hposlen : 0 < p.2.1.length := p.2.1.length_pos_of_pos hrpos
      have hpow : (n + c) ^ p.2.1.length ≤ (n + c) ^ s := by
        have hne1 : p.2.1.length ≠ 0 := Nat.ne_of_gt hposlen
        have hne2 : s ≠ 0 := Nat.ne_of_gt hspos
        simp [hbase, Nat.zero_pow, hne1, hne2]
      exact le_trans hcomp hpow
    · have h1 : 1 ≤ n + c := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hbase)
      have hpow : (n + c) ^ p.2.1.length ≤ (n + c) ^ s := pow_le_pow_right' h1 hlen_le
      exact le_trans hcomp hpow

  have hSum_le : (∑ p : ι, (Words p).ncard) ≤ ∑ p : ι, (n + c) ^ s := by
    classical
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun p hp => hWords_bound p))

  -- evaluate the constant sum using the counting of compositions
  have hcardι : Fintype.card ι = ∑ j : Fin s, (r - 1).choose (j : ℕ) := by
    classical
    have hcard : Fintype.card ι = ∑ j : Fin s, Fintype.card (C j) := by
      simpa [ι] using (Fintype.card_sigma (α := C))
    have hcardC : ∀ j : Fin s, Fintype.card (C j) = (r - 1).choose (j : ℕ) := by
      intro j
      simpa [C] using (composition_card_len_succ r (j := (j : ℕ)) hr)
    have hfun : (fun j : Fin s => Fintype.card (C j)) = fun j : Fin s => (r - 1).choose (j : ℕ) := by
      funext j
      exact hcardC j
    have hsum : (∑ j : Fin s, Fintype.card (C j)) = ∑ j : Fin s, (r - 1).choose (j : ℕ) := by
      simpa [hfun] using (Fintype.sum_congr hfun)
    exact hcard.trans hsum

  have hsumRange : (∑ j : Fin s, (r - 1).choose (j : ℕ)) = ∑ j ∈ Finset.range s, (r - 1).choose j := by
    -- convert the sum over `Fin s` to a sum over `Finset.range s`
    simpa using (Fin.sum_univ_eq_sum_range (f := fun j : ℕ => (r - 1).choose j) (n := s))

  have hConst : (∑ p : ι, (n + c) ^ s) = (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := by
    classical
    calc
      (∑ p : ι, (n + c) ^ s) = Fintype.card ι * (n + c) ^ s := by simp
      _ = (∑ j : Fin s, (r - 1).choose (j : ℕ)) * (n + c) ^ s := by simpa [hcardι]
      _ = (n + c) ^ s * (∑ j : Fin s, (r - 1).choose (j : ℕ)) := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := by
            simpa [hsumRange]

  -- combine all inequalities
  have hfinal : S.ncard ≤ (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := by
    have hmain : S.ncard ≤ ∑ p : ι, (n + c) ^ s :=
      le_trans hS_le_union (le_trans hUnion_le_sum hSum_le)
    simpa [hConst] using (le_trans hmain (le_of_eq hConst))

  simpa [S] using hfinal

theorem ncard_words_length (n r : ℕ) : Set.ncard {w : FreeMonoid (Fin n) | w.length = r} = n ^ r := by
  classical
  -- rewrite the set cardinality as a `Nat.card` of the underlying subtype
  rw [(Nat.card_coe_set_eq (s := {w : FreeMonoid (Fin n) | w.length = r})).symm]
  -- identify words of length `r` with `List.Vector (Fin n) r`
  let e : ({w : FreeMonoid (Fin n) | w.length = r} : Type) ≃ List.Vector (Fin n) r :=
    (FreeMonoid.toList).subtypeEquiv (by
      intro w
      rfl)
  -- compute the cardinality using `card_vector`
  calc
    Nat.card ({w : FreeMonoid (Fin n) | w.length = r} : Type) = Nat.card (List.Vector (Fin n) r) :=
      Nat.card_congr e
    _ = Fintype.card (List.Vector (Fin n) r) := by
      simpa using (Nat.card_eq_fintype_card (α := List.Vector (Fin n) r))
    _ = Fintype.card (Fin n) ^ r := by
      simpa using (card_vector (α := Fin n) r)
    _ = n ^ r := by
      simp

theorem sum_choose_le_exp (N m : ℕ) (hm : 0 < m) (hNm : m ≤ N) :
  (∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ)) ≤ (Real.exp 1 * (N : ℝ) / (m : ℝ)) ^ m := by
  classical
  have hNnat : 0 < N := lt_of_lt_of_le hm hNm
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNnat
  have hmposR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmposR
  set t : ℝ := (m : ℝ) / (N : ℝ) with htdef
  have htpos : 0 < t := by
    have : 0 < (m : ℝ) / (N : ℝ) := div_pos hmposR hNpos
    simpa [htdef] using this
  have ht0 : 0 ≤ t := le_of_lt htpos
  have ht1 : t ≤ 1 := by
    have hmn : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNm
    have : (m : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNpos).2 hmn
    simpa [htdef] using this

  have hbinom : (1 + t) ^ N = ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * t ^ j := by
    simpa [add_comm, add_left_comm, add_assoc, one_pow, mul_assoc, mul_left_comm, mul_comm] using
      (add_pow (t : ℝ) (1 : ℝ) N)

  have hpow_le : ∀ {j : ℕ}, j ∈ Finset.range (m + 1) → t ^ m ≤ t ^ j := by
    intro j hj
    have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simpa using (pow_le_pow_of_le_one ht0 ht1 hjle)

  have hmain1 : t ^ m * (∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ)) ≤
      ∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ) * t ^ j := by
    have hsum : (∑ j ∈ Finset.range (m + 1), t ^ m * (N.choose j : ℝ)) ≤
        ∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ) * t ^ j := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hcoef : 0 ≤ (N.choose j : ℝ) := by exact_mod_cast (Nat.zero_le (N.choose j))
      have ht' : t ^ m ≤ t ^ j := hpow_le hj
      have : (N.choose j : ℝ) * t ^ m ≤ (N.choose j : ℝ) * t ^ j :=
        mul_le_mul_of_nonneg_left ht' hcoef
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    simpa [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hsum

  have hsubset : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
    intro j hj
    have hjlt : j < m + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ m := Nat.le_of_lt_succ hjlt
    have : j ≤ N := le_trans hjle hNm
    exact Finset.mem_range.mpr (lt_of_le_of_lt this (Nat.lt_succ_self N))

  have hmain : t ^ m * (∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ)) ≤ (1 + t) ^ N := by
    have hle2 : (∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ) * t ^ j) ≤
        ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * t ^ j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro j hjt hjnot
      have hcoef : 0 ≤ (N.choose j : ℝ) := by exact_mod_cast (Nat.zero_le (N.choose j))
      have hpow : 0 ≤ t ^ j := pow_nonneg ht0 _
      exact mul_nonneg hcoef hpow
    have htemp : t ^ m * (∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ)) ≤
        ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * t ^ j := le_trans hmain1 hle2
    simpa [hbinom] using htemp

  have hdiv : (∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ)) ≤ (1 + t) ^ N / t ^ m := by
    have htpm_pos : 0 < t ^ m := pow_pos htpos _
    refine (le_div_iff₀ htpm_pos).2 ?_
    -- goal: (sum) * t^m ≤ (1+t)^N
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmain

  have hNt : (N : ℝ) * t = (m : ℝ) := by
    calc
      (N : ℝ) * t = (N : ℝ) * ((m : ℝ) / (N : ℝ)) := by simpa [htdef]
      _ = (m : ℝ) := by
        field_simp [hNne]

  have hexp : (1 + t) ^ N ≤ Real.exp (m : ℝ) := by
    have h1t_le_expt : 1 + t ≤ Real.exp t := by
      simpa [add_comm, add_left_comm, add_assoc] using (Real.add_one_le_exp t)
    have h1t_nonneg : 0 ≤ 1 + t := by linarith [ht0]
    have hpow : (1 + t) ^ N ≤ (Real.exp t) ^ N := by
      -- monotonicity of pow
      exact (pow_le_pow_left₀ h1t_nonneg h1t_le_expt N)
    -- rewrite (exp t)^N = exp (N*t)
    have hpow' : (Real.exp t) ^ N = Real.exp (N * t) := by
      simpa using (Real.exp_nat_mul t N).symm
    -- combine
    calc
      (1 + t) ^ N ≤ (Real.exp t) ^ N := hpow
      _ = Real.exp (N * t) := hpow'
      _ = Real.exp (m : ℝ) := by
        -- simplify N*t
        -- N*t = (N:ℝ)*t
        have : (N : ℝ) * t = (m : ℝ) := hNt
        simpa [Nat.cast_mul, this]

  have hS_le : (∑ j ∈ Finset.range (m + 1), (N.choose j : ℝ)) ≤ Real.exp (m : ℝ) / t ^ m := by
    have hnum : (1 + t) ^ N / t ^ m ≤ Real.exp (m : ℝ) / t ^ m :=
      div_le_div_of_nonneg_right hexp (pow_nonneg ht0 _)
    exact le_trans hdiv hnum

  -- final algebra
  have hfinal : Real.exp (m : ℝ) / t ^ m = (Real.exp 1 * (N : ℝ) / (m : ℝ)) ^ m := by
    -- rewrite exp(m) as (exp 1)^m and t as m/N
    --
    simp [htdef, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Real.exp_one_pow,
      mul_pow, one_div, pow_mul] 

  simpa [hfinal] using (le_trans hS_le (le_of_eq hfinal))


theorem two_mul_log_div_log_two_le_sub_two (x : ℝ) (hx : 8 ≤ x) : 2 * Real.log x / Real.log 2 ≤ x - 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  set z : ℝ := x / 8 with hzdef
  have h8pos : (0 : ℝ) < 8 := by norm_num
  have hz0 : 0 < z := by
    simpa [z] using (div_pos hx0 h8pos)
  have hz1 : 1 ≤ z := by
    have : (8 : ℝ) / 8 ≤ x / 8 := by
      exact div_le_div_of_nonneg_right hx (by norm_num : (0 : ℝ) ≤ 8)
    simpa [z] using this
  have hz_ne : z ≠ 0 := ne_of_gt hz0

  have hxz : x = 8 * z := by
    have h8 : (8 : ℝ) ≠ 0 := by norm_num
    have : (8 : ℝ) * z = x := by
      simpa [z] using (mul_div_cancel₀ (a := x) (b := (8 : ℝ)) h8)
    exact this.symm

  have hlogx : Real.log x = Real.log 8 + Real.log z := by
    have h8 : (8 : ℝ) ≠ 0 := by norm_num
    calc
      Real.log x = Real.log (8 * z) := by simpa [hxz]
      _ = Real.log 8 + Real.log z := by
        simpa using (Real.log_mul h8 hz_ne)

  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    simpa [show ((2 : ℝ) ^ 3) = (8 : ℝ) by norm_num] using
      (Real.log_pow (2 : ℝ) 3)

  have hlog2pos : 0 < Real.log 2 := by
    simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos

  have hterm6 : (2 * Real.log 8) / Real.log 2 = 6 := by
    calc
      (2 * Real.log 8) / Real.log 2 = (2 * (3 * Real.log 2)) / Real.log 2 := by
        simpa [hlog8]
      _ = (6 * Real.log 2) / Real.log 2 := by ring
      _ = 6 := by
        simpa using (mul_div_cancel_right₀ (a := (6 : ℝ)) (b := Real.log 2) hlog2ne)

  have hxexpr : 2 * Real.log x / Real.log 2 = 6 + 2 * Real.log z / Real.log 2 := by
    calc
      2 * Real.log x / Real.log 2 = (2 * (Real.log 8 + Real.log z)) / Real.log 2 := by
        simp [hlogx]
      _ = ((2 * Real.log 8) + (2 * Real.log z)) / Real.log 2 := by
        simp [mul_add]
      _ = (2 * Real.log 8) / Real.log 2 + (2 * Real.log z) / Real.log 2 := by
        simp [add_div]
      _ = 6 + 2 * Real.log z / Real.log 2 := by
        simp [hterm6]

  have hlogz : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos hz0

  have hlog2_lower : (1 / 4 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]

  have hone_div_log2 : (1 : ℝ) / Real.log 2 ≤ 4 := by
    have hquartpos : (0 : ℝ) < (1 / 4 : ℝ) := by norm_num
    have := one_div_le_one_div_of_le hquartpos hlog2_lower
    simpa [one_div] using this

  have htwo_div_log2 : (2 : ℝ) / Real.log 2 ≤ 8 := by
    calc
      (2 : ℝ) / Real.log 2 = (2 : ℝ) * ((1 : ℝ) / Real.log 2) := by
        simp [div_eq_mul_inv, one_div, mul_assoc]
      _ ≤ (2 : ℝ) * 4 := by
        exact mul_le_mul_of_nonneg_left hone_div_log2 (by norm_num : (0 : ℝ) ≤ 2)
      _ = 8 := by norm_num

  have hz1' : 0 ≤ z - 1 := by linarith [hz1]

  have hlogz_term : 2 * Real.log z / Real.log 2 ≤ 8 * (z - 1) := by
    -- compare via the coefficient `2 / log 2`
    have hk_nonneg : 0 ≤ (2 : ℝ) / Real.log 2 := by
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hlog2pos)
    have h1 : (2 / Real.log 2) * Real.log z ≤ (2 / Real.log 2) * (z - 1) := by
      exact mul_le_mul_of_nonneg_left hlogz hk_nonneg
    have h2 : (2 / Real.log 2) * (z - 1) ≤ 8 * (z - 1) := by
      exact mul_le_mul_of_nonneg_right htwo_div_log2 hz1'
    have hcoeff : (2 / Real.log 2) * Real.log z ≤ 8 * (z - 1) := le_trans h1 h2
    have hrewrite : (2 / Real.log 2) * Real.log z = 2 * Real.log z / Real.log 2 := by
      simp [div_eq_mul_inv]
      ac_rfl
    simpa [hrewrite] using hcoeff

  have hxmain : 2 * Real.log x / Real.log 2 ≤ 6 + 8 * (z - 1) := by
    rw [hxexpr]
    -- `add_le_add_right` gives `(2*log z/log 2) + 6 ≤ (8*(z-1)) + 6`
    simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hlogz_term 6)

  have hrhs : 6 + 8 * (z - 1) = x - 2 := by
    calc
      6 + 8 * (z - 1) = 8 * z - 2 := by ring
      _ = x - 2 := by simpa [hxz]

  simpa [hrhs] using hxmain

theorem logDensityD_lt_two_e_mul (n c : ℕ) (hn : 2 ≤ n) :
  (logDensityD n c : ℝ) < 2 * (Real.exp 1) * (n + c) := by
  classical
  let x : ℝ := 2 * Real.exp 1 * (n + c)
  have hx8 : (8 : ℝ) ≤ x := by
    have hncNat : 2 ≤ n + c := le_trans hn (Nat.le_add_right n c)
    have hnc : (2 : ℝ) ≤ (n + c : ℝ) := by
      exact_mod_cast hncNat
    have hexp : (2 : ℝ) ≤ Real.exp 1 := by
      have h := (Real.two_mul_le_exp (x := (1 : ℝ)))
      simpa using h
    have : (8 : ℝ) ≤ 2 * Real.exp 1 * (n + c : ℝ) := by
      nlinarith [hnc, hexp]
    simpa [x, mul_assoc, mul_left_comm, mul_comm] using this

  let y : ℝ := 2 * Real.log x / Real.log n

  have hlog2_le_logn : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := by
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have h2pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have := Real.log_le_log h2pos hn'
    simpa using this

  have hx1 : (1 : ℝ) ≤ x := by
    exact le_trans (by norm_num : (1 : ℝ) ≤ (8 : ℝ)) hx8

  have hlogx_nonneg : 0 ≤ Real.log x := by
    exact Real.log_nonneg hx1

  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < (2 : ℝ) := by norm_num
    simpa using Real.log_pos this

  have hy_le : y ≤ 2 * Real.log x / Real.log (2 : ℝ) := by
    have ha : 0 ≤ 2 * Real.log x := by
      have : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this hlogx_nonneg
    have : (2 * Real.log x) / Real.log (n : ℝ) ≤ (2 * Real.log x) / Real.log (2 : ℝ) := by
      exact div_le_div_of_nonneg_left ha hlog2_pos hlog2_le_logn
    simpa [y] using this

  have hy_le_sub : y ≤ x - 2 := by
    exact le_trans hy_le (two_mul_log_div_log_two_le_sub_two x hx8)

  have hceil_lt : (Int.ceil y : ℝ) < x := by
    have hceil : (Int.ceil y : ℝ) < y + 1 := by
      simpa using (Int.ceil_lt_add_one y)
    have hy1 : y + 1 ≤ x - 1 := by
      linarith [hy_le_sub]
    have hx1' : x - 1 < x := by
      linarith
    have h' : (Int.ceil y : ℝ) < x - 1 := lt_of_lt_of_le hceil hy1
    exact lt_trans h' hx1'

  have htwo_lt : (2 : ℝ) < x := by
    exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < (8 : ℝ)) hx8

  have hmax_lt : (max (2 : ℤ) (Int.ceil y) : ℝ) < x := by
    -- cast max to max of casts
    have hcast : (max (2 : ℤ) (Int.ceil y) : ℝ) = max (2 : ℝ) (Int.ceil y : ℝ) := by
      simpa using (Int.cast_max (a := (2 : ℤ)) (b := Int.ceil y) (R := ℝ))
    have : max (2 : ℝ) (Int.ceil y : ℝ) < x := by
      exact max_lt_iff.mpr ⟨htwo_lt, hceil_lt⟩
    simpa [hcast] using this

  let z : ℤ := max 2 (Int.ceil y)

  have hz_nonneg : (0 : ℤ) ≤ z := by
    -- z ≥ 2
    have : (2 : ℤ) ≤ z := le_max_left 2 (Int.ceil y)
    exact le_trans (by decide : (0 : ℤ) ≤ (2 : ℤ)) this

  have hz_toNat_real : (Int.toNat z : ℝ) = (z : ℝ) := by
    -- cast via ℤ
    have htoNat : ((Int.toNat z : ℤ) : ℝ) = (z : ℝ) := by
      have h := Int.toNat_of_nonneg hz_nonneg
      -- h : (Int.toNat z : ℤ) = z
      have h' := congrArg (fun t : ℤ => (t : ℝ)) h
      simpa using h'
    -- now relate Nat cast and Int cast
    have hnat : (Int.toNat z : ℝ) = ((Int.toNat z : ℤ) : ℝ) := by
      -- Int.cast_natCast : ((n : ℤ) : ℝ) = (n : ℝ)
      simpa using (Int.cast_natCast (R := ℝ) (n := Int.toNat z)).symm
    calc
      (Int.toNat z : ℝ) = ((Int.toNat z : ℤ) : ℝ) := hnat
      _ = (z : ℝ) := htoNat

  have hz_lt : (Int.toNat z : ℝ) < x := by
    -- use hmax_lt (rewritten with z)
    have : (z : ℝ) < x := by
      -- unfold z in hmax_lt
      simpa [z] using hmax_lt
    simpa [hz_toNat_real] using this

  -- unfold logDensityD and substitute x,y,z
  have : (logDensityD n c : ℝ) < x := by
    -- unfold definition
    unfold logDensityD
    -- simplify with x,y,z
    --
    -- logDensityD n c = Int.toNat (max 2 (Int.ceil ...))
    --
    simpa [x, y, z] using hz_lt

  -- finish
  simpa [x, mul_assoc, mul_left_comm, mul_comm, Nat.cast_add] using this


theorem logDensityD_good (n c : ℕ) (hn : 2 ≤ n) :
  (n : ℝ) ^ (logDensityD n c) > 2 * (Real.exp 1) * (logDensityD n c) * (n + c) := by
  classical
  set d : ℕ := logDensityD n c
  set x : ℝ := 2 * (Real.exp 1) * (n + c)
  have hx2 : x ^ 2 ≤ (n : ℝ) ^ d := by
    simpa [x, d] using logDensityD_pow_ge_square n c hn
  have hdlt : (d : ℝ) < x := by
    simpa [x, d] using logDensityD_lt_two_e_mul n c hn
  have hxpos : 0 < x := by
    have hle : 2 ≤ n + c := le_trans hn (Nat.le_add_right n c)
    have hncnat : 0 < n + c := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hle
    have hnc : (0 : ℝ) < (n + c : ℝ) := by
      exact_mod_cast hncnat
    have h2 : (0 : ℝ) < (2 : ℝ) := by
      norm_num
    have he : 0 < Real.exp 1 := by
      positivity
    dsimp [x]
    exact mul_pos (mul_pos h2 he) hnc
  have hxd : x * (d : ℝ) < x ^ 2 := by
    have h : x * (d : ℝ) < x * x := mul_lt_mul_of_pos_left hdlt hxpos
    simpa [pow_two] using h
  have hlt : x * (d : ℝ) < (n : ℝ) ^ d := lt_of_lt_of_le hxd hx2
  have hEq : x * (d : ℝ) = 2 * Real.exp 1 * (d : ℝ) * (n + c) := by
    dsimp [x]
    ring
  have : 2 * Real.exp 1 * (d : ℝ) * (n + c) < (n : ℝ) ^ d := by
    simpa [hEq] using hlt
  simpa [d] using this

theorem theorem_4_logarithmic_density (n : ℕ) (hn : n ≥ 2)
  (G : Set (FreeMonoid (Fin n)))
  (c : ℕ)
  (hG : ∀ l : ℕ, l ≥ 2 → (Set.ncard { x ∈ G | x.length = l } ≤ c)) :
    let d := logDensityD n c
    ∀ (s : ℕ), s ≥ 1 → ¬ (Ball (d * s) (A n) ⊆ Ball s (G ∪ (A n))) := by
  classical
  simp
  intro s hs
  intro hsub
  set d : ℕ := logDensityD n c with hd
  have hd' : logDensityD n c = d := hd.symm
  set r : ℕ := d * s with hr
  have hsub1 : Ball (d * s) (A n) ⊆ Ball s (G ∪ A n) := by
    simpa [hd'] using hsub
  have hsub2 : Ball r (A n) ⊆ Ball s (G ∪ A n) := by
    intro w hw
    apply hsub1
    simpa [hr] using hw
  have hSr : {w : FreeMonoid (Fin n) | w.length = r} ⊆ Ball s (G ∪ A n) := by
    intro w hw
    have hwlen : w.length = r := hw
    have hwA : w ∈ Ball w.length (A n) := mem_Ball_A n w
    have hwAr : w ∈ Ball r (A n) := by
      simpa [hwlen] using hwA
    exact hsub2 hwAr
  have hInter : ({w : FreeMonoid (Fin n) | w.length = r} ∩ Ball s (G ∪ A n)) = {w : FreeMonoid (Fin n) | w.length = r} := by
    exact Set.inter_eq_left.mpr hSr
  have hncard_eq : Set.ncard {w : FreeMonoid (Fin n) | w.length = r} =
      Set.ncard ({w : FreeMonoid (Fin n) | w.length = r} ∩ Ball s (G ∪ A n)) := by
    have := congrArg Set.ncard hInter
    simpa using this.symm
  have hs1 : 1 ≤ s := hs
  have hd2 : 2 ≤ d := by
    simpa [hd] using (logDensityD_ge_two n c)
  have hr1 : 1 ≤ r := by
    have hdpos : 0 < d := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hd2
    have hspos : 0 < s := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hs1
    have : 0 < d * s := Nat.mul_pos hdpos hspos
    have : 0 < r := by simpa [hr] using this
    exact Nat.succ_le_iff.mp this
  have hbound : Set.ncard ({w : FreeMonoid (Fin n) | w.length = r} ∩ Ball s (G ∪ A n)) ≤
      (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := by
    simpa using (ncard_len_inter_ball_le n G c hG r s hr1 hs1)
  have hncard_le : Set.ncard {w : FreeMonoid (Fin n) | w.length = r} ≤
      (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := by
    calc
      Set.ncard {w : FreeMonoid (Fin n) | w.length = r}
          = Set.ncard ({w : FreeMonoid (Fin n) | w.length = r} ∩ Ball s (G ∪ A n)) := hncard_eq
      _ ≤ (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := hbound
  have hkey_nat : n ^ r ≤ (n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) := by
    simpa [ncard_words_length n r] using hncard_le
  by_cases hs_eq1 : s = 1
  · subst hs_eq1
    have hr_eq : r = d := by
      simpa [hr]
    have hkey1 : n ^ r ≤ n + c := by
      simpa using hkey_nat
    have hkey1R : (n : ℝ) ^ r ≤ (n + c : ℝ) := by
      exact_mod_cast hkey1
    have hlog : (n : ℝ) ^ d > 2 * Real.exp 1 * d * (n + c) := by
      simpa [hd] using (logDensityD_good n c hn)
    have hkeydR : (n : ℝ) ^ d ≤ (n + c : ℝ) := by
      simpa [hr_eq] using hkey1R
    have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by
      simpa using (Real.one_le_exp (show (0 : ℝ) ≤ (1 : ℝ) by linarith))
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      have : (1 : ℕ) ≤ d := le_trans (by decide : (1 : ℕ) ≤ 2) hd2
      exact_mod_cast this
    have hfactor : (1 : ℝ) ≤ 2 * Real.exp 1 * (d : ℝ) := by
      nlinarith [hexp1, hd1]
    have hmul : (n + c : ℝ) ≤ 2 * Real.exp 1 * (d : ℝ) * (n + c : ℝ) := by
      have hnc : (0 : ℝ) ≤ (n + c : ℝ) := by exact_mod_cast (Nat.zero_le (n + c))
      have := mul_le_mul_of_nonneg_right hfactor hnc
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have : (n : ℝ) ^ d ≤ 2 * Real.exp 1 * (d : ℝ) * (n + c : ℝ) := le_trans hkeydR hmul
    exact (not_le_of_gt hlog) this
  ·
    have hs2 : 2 ≤ s := by
      have hne : (1 : ℕ) ≠ s := by
        symm
        exact hs_eq1
      have hlt : 1 < s := lt_of_le_of_ne hs1 hne
      exact (Nat.succ_le_iff.mp hlt)
    let m : ℕ := s - 1
    have hmpos : 0 < m := by
      have : 0 < s - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hs2)
      simpa [m] using this
    have hm_le : m ≤ r - 1 := by
      have hs_le_r : s ≤ r := by
        have hd1 : 1 ≤ d := le_trans (by decide : (1 : ℕ) ≤ 2) hd2
        have : s ≤ d * s := by
          simpa [Nat.one_mul] using (Nat.mul_le_mul_right s hd1)
        simpa [hr] using this
      have : s - 1 ≤ r - 1 := Nat.sub_le_sub_right hs_le_r 1
      simpa [m] using this
    have hkey_real : (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s *
        (∑ j ∈ Finset.range s, ((r - 1).choose j : ℝ)) := by
      have : (n ^ r : ℝ) ≤ ((n + c) ^ s * (∑ j ∈ Finset.range s, (r - 1).choose j) : ℝ) := by
        exact_mod_cast hkey_nat
      simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_sum] using this
    have hsum_le : (∑ j ∈ Finset.range s, ((r - 1).choose j : ℝ)) ≤
        (Real.exp 1 * ((r - 1 : ℕ) : ℝ) / (m : ℝ)) ^ m := by
      have hNm : m ≤ r - 1 := hm_le
      have htmp := sum_choose_le_exp (r - 1) m hmpos hNm
      have hm1 : m + 1 = s := by
        simp [m, Nat.sub_add_cancel hs1]
      simpa [hm1, Nat.cast_sub, hs1, m] using htmp
    have hkey_real2 : (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s * (Real.exp 1 * ((r - 1 : ℕ) : ℝ) / (m : ℝ)) ^ m := by
      calc
        (n : ℝ) ^ r
            ≤ (n + c : ℝ) ^ s * (∑ j ∈ Finset.range s, ((r - 1).choose j : ℝ)) := hkey_real
        _ ≤ (n + c : ℝ) ^ s * (Real.exp 1 * ((r - 1 : ℕ) : ℝ) / (m : ℝ)) ^ m := by
          gcongr
    set B : ℝ := Real.exp 1 * ((r - 1 : ℕ) : ℝ) / (m : ℝ)
    have hkeyB : (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s * B ^ m := by
      simpa [B] using hkey_real2
    have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hB_ratio : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (m : ℝ) := by
      have hcast : (m : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
        exact_mod_cast hm_le
      exact (one_le_div hmposR).2 hcast
    have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by
      simpa using (Real.one_le_exp (show (0 : ℝ) ≤ (1 : ℝ) by linarith))
    have hB_ge1 : (1 : ℝ) ≤ B := by
      have : (1 : ℝ) ≤ Real.exp 1 * (((r - 1 : ℕ) : ℝ) / (m : ℝ)) := by
        nlinarith [hexp1, hB_ratio]
      simpa [B, mul_div_assoc] using this
    have hm_le_s : m ≤ s := Nat.sub_le _ _
    have hBpow : B ^ m ≤ B ^ s := pow_le_pow_right₀ hB_ge1 hm_le_s
    have hnc_nonneg : (0 : ℝ) ≤ (n + c : ℝ) ^ s := by
      have : (0 : ℝ) ≤ (n + c : ℝ) := by exact_mod_cast (Nat.zero_le (n + c))
      exact pow_nonneg this _
    have hkeyB2 : (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s * B ^ s := by
      calc
        (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s * B ^ m := hkeyB
        _ ≤ (n + c : ℝ) ^ s * B ^ s := by
          exact mul_le_mul_of_nonneg_left hBpow hnc_nonneg
    have hs_le_two : s ≤ 2 * (s - 1) := by
      have hs1' : 1 ≤ s - 1 := by
        have : 0 < s - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hs2)
        exact Nat.succ_le_iff.mp this
      have htmp : (s - 1) + 1 ≤ (s - 1) + (s - 1) := by
        exact Nat.add_le_add_left hs1' (s - 1)
      have htmp2 : (s - 1) + 1 ≤ 2 * (s - 1) := by
        simpa [two_mul] using htmp
      simpa [Nat.sub_add_cancel hs1] using htmp2
    have hs1R : (0 : ℝ) < (s - 1 : ℝ) := by
      have : 0 < s - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hs2)
      exact_mod_cast this
    have hsr_div : (s : ℝ) / (s - 1 : ℝ) ≤ (2 : ℝ) := by
      have hsineq : (s : ℝ) ≤ (2 : ℝ) * (s - 1 : ℝ) := by
        have : (s : ℝ) ≤ (2 * (s - 1) : ℕ) := by
          exact_mod_cast hs_le_two
        simpa [Nat.cast_mul, Nat.cast_sub, hs1] using this
      exact (div_le_iff₀ hs1R).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hsineq)
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
    have hr_div : (r : ℝ) / (s - 1 : ℝ) ≤ (2 : ℝ) * (d : ℝ) := by
      have : (r : ℝ) / (s - 1 : ℝ) = (d : ℝ) * ((s : ℝ) / (s - 1 : ℝ)) := by
        simp [hr, Nat.cast_mul, mul_div_assoc]
      calc
        (r : ℝ) / (s - 1 : ℝ) = (d : ℝ) * ((s : ℝ) / (s - 1 : ℝ)) := this
        _ ≤ (d : ℝ) * (2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsr_div hd_nonneg
        _ = (2 : ℝ) * (d : ℝ) := by
          ring
    have hmposR0 : (0 : ℝ) ≤ (m : ℝ) := le_of_lt hmposR
    have hB_le : B ≤ 2 * Real.exp 1 * (d : ℝ) := by
      have hrr : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
        have : r - 1 ≤ r := Nat.sub_le r 1
        exact_mod_cast this
      have hdiv : ((r - 1 : ℕ) : ℝ) / (m : ℝ) ≤ (r : ℝ) / (m : ℝ) := by
        exact div_le_div_of_nonneg_right hrr hmposR0
      have hmul1 : Real.exp 1 * (((r - 1 : ℕ) : ℝ) / (m : ℝ)) ≤ Real.exp 1 * ((r : ℝ) / (m : ℝ)) := by
        have hexp0 : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
        exact mul_le_mul_of_nonneg_left hdiv hexp0
      have hm_cast : (m : ℝ) = (s - 1 : ℝ) := by
        simp [m, Nat.cast_sub, hs1]
      have hr_div' : (r : ℝ) / (m : ℝ) ≤ 2 * (d : ℝ) := by
        simpa [hm_cast] using hr_div
      have hmul2 : Real.exp 1 * ((r : ℝ) / (m : ℝ)) ≤ Real.exp 1 * (2 * (d : ℝ)) := by
        have hexp0 : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
        exact mul_le_mul_of_nonneg_left hr_div' hexp0
      have hmul3 : Real.exp 1 * (2 * (d : ℝ)) = 2 * Real.exp 1 * (d : ℝ) := by
        ring
      have : Real.exp 1 * (((r - 1 : ℕ) : ℝ) / (m : ℝ)) ≤ 2 * Real.exp 1 * (d : ℝ) := by
        calc
          Real.exp 1 * (((r - 1 : ℕ) : ℝ) / (m : ℝ))
              ≤ Real.exp 1 * ((r : ℝ) / (m : ℝ)) := hmul1
          _ ≤ Real.exp 1 * (2 * (d : ℝ)) := hmul2
          _ = 2 * Real.exp 1 * (d : ℝ) := by simpa [hmul3]
      simpa [B, mul_div_assoc] using this
    have hB_nonneg : (0 : ℝ) ≤ B := le_trans (show (0 : ℝ) ≤ (1 : ℝ) by linarith) hB_ge1
    have hBpow2 : B ^ s ≤ (2 * Real.exp 1 * (d : ℝ)) ^ s := by
      exact (pow_le_pow_left₀ hB_nonneg hB_le s)
    have hkey_final : (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s * (2 * Real.exp 1 * (d : ℝ)) ^ s := by
      calc
        (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s * B ^ s := hkeyB2
        _ ≤ (n + c : ℝ) ^ s * (2 * Real.exp 1 * (d : ℝ)) ^ s := by
          exact mul_le_mul_of_nonneg_left hBpow2 hnc_nonneg
    have hkey_pow : ((n : ℝ) ^ d) ^ s ≤ ((n + c : ℝ) * (d : ℝ) * (2 * Real.exp 1)) ^ s := by
      have hL : (n : ℝ) ^ r = ((n : ℝ) ^ d) ^ s := by
        simpa [hr, pow_mul]
      -- rewrite RHS using `mul_pow`
      have hR : (n + c : ℝ) ^ s * ((d : ℝ) * (2 * Real.exp 1)) ^ s =
          ((n + c : ℝ) * ((d : ℝ) * (2 * Real.exp 1))) ^ s := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_pow (n + c : ℝ) ((d : ℝ) * (2 * Real.exp 1)) s).symm
      -- use commutativity to match `hkey_final`
      have hkey_final' : (n : ℝ) ^ r ≤ (n + c : ℝ) ^ s * ((d : ℝ) * (2 * Real.exp 1)) ^ s := by
        -- just rewrite factors in `hkey_final`
        simpa [mul_assoc, mul_left_comm, mul_comm] using hkey_final
      -- combine
      calc
        ((n : ℝ) ^ d) ^ s = (n : ℝ) ^ r := by simpa [hL]
        _ ≤ (n + c : ℝ) ^ s * ((d : ℝ) * (2 * Real.exp 1)) ^ s := hkey_final'
        _ = ((n + c : ℝ) * ((d : ℝ) * (2 * Real.exp 1))) ^ s := hR
        _ = ((n + c : ℝ) * (d : ℝ) * (2 * Real.exp 1)) ^ s := by
          ring_nf
    have hlog : (n : ℝ) ^ d > 2 * Real.exp 1 * d * (n + c) := by
      simpa [hd] using (logDensityD_good n c hn)
    have hlog' : ((n + c : ℝ) * (d : ℝ) * (2 * Real.exp 1)) ^ s < ((n : ℝ) ^ d) ^ s := by
      have ha0 : (0 : ℝ) ≤ (n + c : ℝ) * (d : ℝ) * (2 * Real.exp 1) := by
        have h0e : (0 : ℝ) ≤ Real.exp 1 := le_of_lt (Real.exp_pos 1)
        have h0d : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
        have h0nc : (0 : ℝ) ≤ (n + c : ℝ) := by exact_mod_cast (Nat.zero_le (n + c))
        nlinarith [h0e, h0d, h0nc]
      have hlt : (n + c : ℝ) * (d : ℝ) * (2 * Real.exp 1) < (n : ℝ) ^ d := by
        -- rewrite `hlog`
        have := hlog
        -- `hlog` is (n^d) > 2*e*d*(n+c)
        -- put RHS in our order
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      have hs_ne0 : s ≠ 0 := by
        exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hs2)
      have := pow_lt_pow_left₀ hlt ha0 (n := s) hs_ne0
      simpa using this
    have : ((n + c : ℝ) * (d : ℝ) * (2 * Real.exp 1)) ^ s <
        ((n + c : ℝ) * (d : ℝ) * (2 * Real.exp 1)) ^ s :=
      lt_of_lt_of_le hlog' hkey_pow
    exact lt_irrefl _ this

