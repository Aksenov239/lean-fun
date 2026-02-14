import Mathlib
import Mathlib.Data.List.Indexes
import Mathlib.Data.Multiset.ZeroCons

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

theorem ball_A_mem_iff_card_le {n : ℕ} (R : ℕ) (m : FreeAbelianMonoid n) :
  m ∈ Ball R (A n) ↔ m.card ≤ R := by
  classical
  constructor
  · intro hm
    rcases hm with ⟨l, hlR, hlA, hsum⟩
    have hcard_sum : (l.sum).card = (l.map Multiset.card).sum := by
      simpa using
        ((Multiset.cardHom : Multiset (Fin n) →+ ℕ).map_list_sum l)
    have hmcard : m.card = (l.map Multiset.card).sum := by
      simpa [hsum] using hcard_sum
    have hsum1 : (l.map Multiset.card).sum = l.length := by
      -- auxiliary lemma: if all elements are singleton, sum of cards is length
      have haux :
          ∀ l : List (FreeAbelianMonoid n),
            (∀ x, x ∈ l → x ∈ A n) → (l.map Multiset.card).sum = l.length := by
        intro l hlA
        induction l with
        | nil =>
            simp
        | cons a t ih =>
            have haA : a ∈ A n := hlA a (by simp)
            rcases haA with ⟨i, rfl⟩
            have htA : ∀ x, x ∈ t → x ∈ A n := by
              intro x hx
              exact hlA x (by simp [hx])
            have iht : (t.map Multiset.card).sum = t.length := ih htA
            -- card {i} = 1
            simp [iht, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      exact haux l hlA
    have hcard_eq_len : m.card = l.length := by
      calc
        m.card = (l.map Multiset.card).sum := hmcard
        _ = l.length := hsum1
    exact le_trans (le_of_eq hcard_eq_len) hlR
  · intro hm
    let f : Fin n → Multiset (Fin n) := fun i => ({i} : Multiset (Fin n))
    refine ⟨(m.map f).toList, ?_, ?_, ?_⟩
    · -- length bound
      have hlen : ((m.map f).toList).length = m.card := by
        calc
          ((m.map f).toList).length = (m.map f).card := by
            simpa using (Multiset.length_toList (s := m.map f))
          _ = m.card := by
            simpa using (Multiset.card_map f m)
      exact le_trans (le_of_eq hlen) hm
    · -- elements are in A n
      intro x hx
      have hx' : x ∈ m.map f := by
        simpa using (Multiset.mem_toList.1 hx)
      rcases (Multiset.mem_map.1 hx') with ⟨i, hi, hix⟩
      refine ⟨i, ?_⟩
      simpa [f] using hix
    · -- sum is m
      calc
        ((m.map f).toList).sum = (((m.map f).toList : Multiset (Multiset (Fin n))).sum) := by
          simpa using (Multiset.sum_coe (l := (m.map f).toList)).symm
        _ = (m.map f).sum := by
          simpa [Multiset.coe_toList]
        _ = m := by
          simpa [f] using (Multiset.sum_map_singleton (s := m))

theorem ball_mono_radius {n : ℕ} {R S : ℕ} {X : Set (FreeAbelianMonoid n)} :
  R ≤ S → Ball R X ⊆ Ball S X := by
  intro hRS
  intro m hm
  rcases hm with ⟨l, hlR, hsum⟩
  refine ⟨l, ?_, hsum⟩
  exact le_trans hlR hRS


theorem ball_mono_set {n : ℕ} {R : ℕ} {X Y : Set (FreeAbelianMonoid n)} :
  X ⊆ Y → Ball R X ⊆ Ball R Y := by
  intro hXY
  intro m hm
  -- unfold membership in Ball
  simp [Ball] at hm ⊢
  rcases hm with ⟨l, hlR, hlX, hsum⟩
  refine ⟨l, hlR, ?_, hsum⟩
  intro x hx
  exact hXY (hlX x hx)
  

def compressList (n b : ℕ) (i : Fin n) (x : ℕ) : List (FreeAbelianMonoid n) :=
  let ds := Nat.digits b x
  let blocks := ds.mapIdx (fun j d => List.replicate d (Multiset.replicate (b ^ j) i))
  blocks.flatten

theorem compressList_mem (n b : ℕ) (i : Fin n) (x : ℕ) :
  ∀ m ∈ compressList n b i x, m ∈ (MacroSet n b ∪ A n) := by
  classical
  intro m hm
  rcases (by
    simpa [compressList] using hm) with ⟨j, -, rfl⟩
  -- turn the union membership into a disjunction
  simp [Set.mem_union]
  cases j with
  | zero =>
      -- j = 0 gives a singleton, hence in A n
      refine Or.inr ?_
      refine ⟨i, ?_⟩
      -- definitional
      simp [pow_zero, Multiset.replicate_one]
  | succ j =>
      -- j ≥ 1 gives a macro element
      refine Or.inl ?_
      refine ⟨i, Nat.succ j, ?_, rfl⟩
      exact Nat.succ_le_succ (Nat.zero_le j)

theorem digits_sum_le_of_le_pow (b k x : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) :
  x ≤ b ^ k → (Nat.digits b x).sum ≤ (b - 1) * k := by
  intro hx
  have hb1 : 1 < b := lt_of_lt_of_le (Nat.lt_succ_self 1) hb
  cases lt_or_eq_of_le hx with
  | inl hxlt =>
      have hlen : (Nat.digits b x).length ≤ k :=
        (Nat.digits_length_le_iff (b := b) (k := k) hb1 x).2 hxlt
      have hsum' : (Nat.digits b x).sum ≤ (Nat.digits b x).length * (b - 1) := by
        have hsum : (Nat.digits b x).sum ≤ (Nat.digits b x).length • (b - 1) := by
          refine List.sum_le_card_nsmul (l := Nat.digits b x) (n := (b - 1)) ?_
          intro d hd
          have hdlt : d < b := Nat.digits_lt_base hb1 hd
          exact Order.le_sub_one_of_lt hdlt
        simpa [Nat.nsmul_eq_mul] using hsum
      have hsum'' : (Nat.digits b x).sum ≤ k * (b - 1) :=
        le_trans hsum' (Nat.mul_le_mul_right (b - 1) hlen)
      exact le_trans hsum'' (le_of_eq (Nat.mul_comm k (b - 1)))
  | inr hxeq =>
      subst hxeq
      have hd1 : Nat.digits b 1 = [1] := by
        simpa using
          (Nat.digits_of_lt (b := b) (x := 1) (by decide : (1 : ℕ) ≠ 0) hb1)
      have hdigits : Nat.digits b (b ^ k) = List.replicate k 0 ++ [1] := by
        simpa [Nat.mul_one, hd1] using
          (Nat.digits_base_pow_mul (b := b) (k := k) (m := 1) hb1 (by decide : (0 : ℕ) < 1))
      have hsumdigits : (Nat.digits b (b ^ k)).sum = 1 := by
        simp [hdigits, List.sum_append, List.sum_replicate]
      have hbsub : 1 ≤ b - 1 := Order.le_sub_one_of_lt hb1
      have hone : 1 ≤ (b - 1) * k := by
        simpa using (Nat.mul_le_mul hbsub hk)
      simpa [hsumdigits] using hone

theorem floor_beta_mul_le_s (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    let β : ℝ := (s : ℝ) / (n * (b - 1))
    let k : ℕ := Int.toNat (Int.floor β)
    n * (b - 1) * k ≤ s := by
  intro s hs
  dsimp
  set β : ℝ := (s : ℝ) / (n * (b - 1))
  set k : ℕ := Int.toNat (Int.floor β)

  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h1
    linarith

  have hb_pos : (0 : ℝ) < (b : ℝ) - 1 := by
    have hb2 : (2 : ℝ) ≤ (b : ℝ) := by
      exact_mod_cast hb
    linarith

  have hb1 : (1 : ℕ) ≤ b := by
    exact le_trans (by decide : (1 : ℕ) ≤ 2) hb

  have hd_pos : (0 : ℝ) < (n * (b - 1) : ℝ) := by
    have : (0 : ℝ) < (n : ℝ) * ((b : ℝ) - 1) := mul_pos hn_pos hb_pos
    -- rewrite cast of nat product
    simpa [Nat.cast_mul, Nat.cast_sub hb1, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using this

  have hβ_nonneg : (0 : ℝ) ≤ β := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (Nat.zero_le s)
    have : (0 : ℝ) ≤ (s : ℝ) / (n * (b - 1) : ℝ) := by
      exact div_nonneg hs0 (le_of_lt hd_pos)
    simpa [β] using this

  have hfloorle : (Int.floor β : ℝ) ≤ β := by
    simpa using (Int.floor_le β)

  have hfloor_nonneg : (0 : ℤ) ≤ Int.floor β := by
    exact (Int.floor_nonneg (a := β)).2 hβ_nonneg

  have hk_int : (k : ℤ) = Int.floor β := by
    have : ((Int.floor β).toNat : ℤ) = Int.floor β := Int.toNat_of_nonneg hfloor_nonneg
    simpa [k] using this

  have hk_real : (k : ℝ) = (Int.floor β : ℝ) := by
    exact_mod_cast hk_int

  have hk_le : (k : ℝ) ≤ β := by
    simpa [hk_real] using hfloorle

  have hk_mul_le : (k : ℝ) * (n * (b - 1) : ℝ) ≤ (s : ℝ) := by
    have : (k : ℝ) ≤ (s : ℝ) / (n * (b - 1) : ℝ) := by
      simpa [β] using hk_le
    have := (le_div_iff₀ hd_pos).1 this
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

  have hcast : ((n * (b - 1) * k : ℕ) : ℝ) ≤ (s : ℝ) := by
    -- rewrite to match hk_mul_le
    simpa [Nat.cast_mul, Nat.cast_sub hb1, Nat.cast_one, mul_assoc, mul_left_comm, mul_comm] using hk_mul_le

  exact_mod_cast hcast

def hardElement (n b k : ℕ) : FreeAbelianMonoid n :=
  Finset.univ.sum (fun i : Fin n => Multiset.replicate (b ^ k - 1) i)

theorem hardElement_card (n b k : ℕ) : (hardElement n b k).card = n * (b ^ k - 1) := by
  classical
  unfold hardElement
  calc
    (∑ i : Fin n, Multiset.replicate (b ^ k - 1) i).card
        = ∑ i : Fin n, (Multiset.replicate (b ^ k - 1) i).card := by
            simpa using
              (Multiset.card_sum (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n => Multiset.replicate (b ^ k - 1) i))
    _ = ∑ _i : Fin n, (b ^ k - 1) := by
            simp [Multiset.card_replicate]
    _ = n * (b ^ k - 1) := by
            simpa using (Fin.sum_const (n := n) (b := (b ^ k - 1)))

theorem hardElement_count (n b k : ℕ) (i : Fin n) : (hardElement n b k).count i = b ^ k - 1 := by
  classical
  -- Rewrite `count` using the additive monoid homomorphism `countAddMonoidHom`.
  -- Then push it through the Finset sum and evaluate.
  rw [← Multiset.coe_countAddMonoidHom i]
  -- now goal is about `countAddMonoidHom` applied to a sum
  simp [hardElement, AddMonoidHom.finset_sum_apply, Multiset.count_replicate,
    Finset.sum_ite_eq', Finset.mem_univ, eq_comm]

theorem list_length_flatten_eq_sum_lengths {α : Type*} (L : List (List α)) :
  L.flatten.length = (L.map List.length).sum := by
  induction L with
  | nil =>
      simp
  | cons l L ih =>
      simp [List.flatten, ih, List.length_append, Nat.add_assoc]


theorem list_sum_map_multiset_replicate {α : Type*} [AddCommMonoid α] (a : α) :
  ∀ l : List ℕ, (l.map (fun n => n • a)).sum = l.sum • a := by
  intro l
  induction l with
  | nil =>
      simp
  | cons n l ih =>
      simp [List.sum_cons, ih, add_nsmul]

theorem macroSet_log_density (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∃ (d1 d2 : Real), ∀ (x : ℕ), x ≥ b → 0 < d1 ∧ 0 < d2
    ∧ d1 * (Real.log x) ≤ ((MacroSet n b) ∩ (Ball x (A n))).ncard
    ∧ ((MacroSet n b) ∩ (Ball x (A n))).ncard ≤ d2 * (Real.log x) := by
  classical
  refine ⟨(n : ℝ) / (2 * Real.log b), (n : ℝ) / (Real.log b), ?_⟩
  intro x hx
  -- basic facts
  have hb1 : 1 < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
  have hb0 : b ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb)
  have hx0 : x ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) (le_trans hb hx))
  have hlogb_pos : 0 < Real.log b := by
    have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
    simpa using Real.log_pos this
  have hnpos : 0 < (n : ℝ) := by
    have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) h1
    exact_mod_cast hn0
  have hd1pos : 0 < (n : ℝ) / (2 * Real.log b) := by
    have hden : 0 < (2 : ℝ) * Real.log b := by nlinarith
    exact div_pos hnpos hden
  have hd2pos : 0 < (n : ℝ) / Real.log b := by
    exact div_pos hnpos hlogb_pos
  -- set up counting
  let T : Set ℕ := {j | 1 ≤ j ∧ b ^ j ≤ x}
  let f : (Fin n × ℕ) → FreeAbelianMonoid n := fun p => Multiset.replicate (b ^ p.2) p.1
  have hf_inj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hrep
    have hpow : b ^ j = b ^ j' := by
      have := congrArg Multiset.card hrep
      simpa [f, Multiset.card_replicate] using this
    have hj : j = j' := (Nat.pow_right_injective hb) hpow
    subst hj
    have hne : b ^ j ≠ 0 := by exact pow_ne_zero _ hb0
    have hi : i = i' := by
      have hrep' : Multiset.replicate (b ^ j) i = Multiset.replicate (b ^ j) i' := by
        simpa [f] using hrep
      exact (Multiset.replicate_right_inj (a := i) (b := i') (n := b ^ j) hne).1 hrep'
    subst hi
    rfl
  have hInter : (MacroSet n b ∩ Ball x (A n)) = f '' ((Set.univ : Set (Fin n)) ×ˢ T) := by
    ext m
    constructor
    · rintro ⟨hmM, hmB⟩
      rcases hmM with ⟨i, j, hj1, rfl⟩
      have hjle : b ^ j ≤ x := by
        have hcard := (ball_A_mem_iff_card_le (n := n) x (Multiset.replicate (b ^ j) i)).1 hmB
        simpa [Multiset.card_replicate] using hcard
      refine ⟨(i, j), ?_, rfl⟩
      simp [T, hj1, hjle]
    · rintro ⟨p, hp, rfl⟩
      -- unpack membership in the product
      have hp' : p.1 ∈ (Set.univ : Set (Fin n)) ∧ p.2 ∈ T := by
        simpa [Set.mem_prod] using hp
      have hp2 : p.2 ∈ T := hp'.2
      have hp2' : 1 ≤ p.2 ∧ b ^ p.2 ≤ x := by simpa [T] using hp2
      have hj1 : 1 ≤ p.2 := hp2'.1
      have hjle : b ^ p.2 ≤ x := hp2'.2
      refine ⟨?_, ?_⟩
      · refine ⟨p.1, p.2, hj1, rfl⟩
      · have hcard : (Multiset.replicate (b ^ p.2) p.1).card ≤ x := by
          simpa [Multiset.card_replicate] using hjle
        exact (ball_A_mem_iff_card_le (n := n) x (Multiset.replicate (b ^ p.2) p.1)).2 hcard
  have hncard_inter : (MacroSet n b ∩ Ball x (A n)).ncard = (((Set.univ : Set (Fin n)) ×ˢ T).ncard) := by
    calc
      (MacroSet n b ∩ Ball x (A n)).ncard = (f '' ((Set.univ : Set (Fin n)) ×ˢ T)).ncard := by
        simpa [hInter]
      _ = (((Set.univ : Set (Fin n)) ×ˢ T).ncard) := by
        simpa using (Set.ncard_image_of_injective ((Set.univ : Set (Fin n)) ×ˢ T) hf_inj)
  -- rewrite T using Nat.log
  let k : ℕ := Nat.log b x
  have hkpos : 1 ≤ k := by
    have hb_le_x : b ^ 1 ≤ x := by simpa using hx
    have := Nat.le_log_of_pow_le hb1 hb_le_x
    simpa [k] using this
  have hT : T = Set.Icc 1 k := by
    ext j
    have hpowlog : b ^ j ≤ x ↔ j ≤ k := by
      simpa [k] using (Nat.pow_le_iff_le_log (b := b) hb1 (x := j) (y := x) hx0)
    simp [T, Set.mem_Icc, hpowlog]
  have hIcc_ncard : (Set.Icc (1 : ℕ) k).ncard = k := by
    have hcard : Nat.card (Set.Icc (1 : ℕ) k) = k := by
      -- compute the card of Icc as a finite type
      simpa [Nat.card_eq_fintype_card] using (Nat.card_fintypeIcc (a := (1 : ℕ)) (b := k))
    -- `Nat.card` of a set is definitional equal to `Set.ncard`
    simpa using (Nat.card_coe_set_eq (s := Set.Icc (1 : ℕ) k)).symm.trans hcard
  have hTncard : T.ncard = k := by
    simpa [hT] using hIcc_ncard
  have hmain_card : (MacroSet n b ∩ Ball x (A n)).ncard = n * k := by
    have huniv : ((Set.univ : Set (Fin n)).ncard) = n := by
      simpa using (Set.ncard_univ (Fin n)).trans (Nat.card_fin n)
    calc
      (MacroSet n b ∩ Ball x (A n)).ncard = (((Set.univ : Set (Fin n)) ×ˢ T).ncard) := hncard_inter
      _ = ((Set.univ : Set (Fin n)).ncard * T.ncard) := by
        simpa using (Set.ncard_prod (s := (Set.univ : Set (Fin n))) (t := T))
      _ = n * k := by simpa [huniv, hTncard]
  -- logarithmic bounds for k
  have hbpos_nat : 0 < b := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hb
  have hxpos_nat : 0 < x := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) (le_trans hb hx)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hbpos_nat
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxpos_nat
  have hpow_nat : b ^ k ≤ x := by
    simpa [k] using (Nat.pow_log_le_self b (x := x) hx0)
  have hpow_real : (b : ℝ) ^ k ≤ x := by
    have : ((b ^ k : ℕ) : ℝ) ≤ x := by exact_mod_cast hpow_nat
    simpa [Nat.cast_pow] using this
  have hk_log : (k : ℝ) * Real.log b ≤ Real.log x :=
    (Real.pow_le_iff_le_log hbpos hxpos).1 hpow_real
  have hk_le : (k : ℝ) ≤ Real.log x / Real.log b := by
    exact (le_div_iff₀ hlogb_pos).2 hk_log
  have hx_lt_pow_nat : x < b ^ k.succ := by
    simpa [k] using (Nat.lt_pow_succ_log_self (b := b) hb1 x)
  have hx_lt_pow_real : (x : ℝ) < (b : ℝ) ^ k.succ := by
    have : ((x : ℕ) : ℝ) < ((b ^ k.succ : ℕ) : ℝ) := by exact_mod_cast hx_lt_pow_nat
    simpa [Nat.cast_pow] using this
  have hlogx_lt : Real.log x < (k.succ : ℝ) * Real.log b :=
    (Real.lt_pow_iff_log_lt hxpos hbpos).1 hx_lt_pow_real
  have hk_succ_le_two : k.succ ≤ 2 * k := by
    omega
  have hk_succ_le_two_real : (k.succ : ℝ) ≤ (2 * k : ℝ) := by
    exact_mod_cast hk_succ_le_two
  have hlogx_le_two : Real.log x ≤ (2 * k : ℝ) * Real.log b := by
    have h1 : Real.log x ≤ (k.succ : ℝ) * Real.log b := le_of_lt hlogx_lt
    have h2 : (k.succ : ℝ) * Real.log b ≤ (2 * k : ℝ) * Real.log b := by
      exact mul_le_mul_of_nonneg_right hk_succ_le_two_real (le_of_lt hlogb_pos)
    exact le_trans h1 h2
  have hlog_div_le : Real.log x / (2 * Real.log b) ≤ (k : ℝ) := by
    have hden : 0 < (2 : ℝ) * Real.log b := by nlinarith
    -- use `div_le_iff₀`
    refine (div_le_iff₀ hden).2 ?_
    -- show `log x ≤ k * (2 * log b)`
    have : (k : ℝ) * ((2 : ℝ) * Real.log b) = (2 * k : ℝ) * Real.log b := by
      ring
    simpa [this] using hlogx_le_two
  refine ⟨hd1pos, hd2pos, ?_, ?_⟩
  · -- lower bound
    -- rewrite ncard
    rw [hmain_card]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hnk : (n : ℝ) * (Real.log x / (2 * Real.log b)) ≤ (n : ℝ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hlog_div_le hn_nonneg
    -- rewrite to the goal
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hnk
  · -- upper bound
    rw [hmain_card]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hnk : (n : ℝ) * (k : ℝ) ≤ (n : ℝ) * (Real.log x / Real.log b) :=
      mul_le_mul_of_nonneg_left hk_le hn_nonneg
    -- rewrite
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, mul_div_assoc', div_mul_eq_mul_div] using hnk


theorem macroUnionA_count_pos_pow (n b : ℕ) (hb : 2 ≤ b) {m : FreeAbelianMonoid n} {i : Fin n} :
  m ∈ (MacroSet n b ∪ A n) → 0 < m.count i → ∃ j : ℕ, m.count i = b ^ j := by
  intro hm hpos
  have hm' : m ∈ MacroSet n b ∨ m ∈ A n := by
    simpa [Set.mem_union] using hm
  cases hm' with
  | inl hM =>
      rcases (by simpa [MacroSet] using hM) with ⟨i0, j0, hj0, rfl⟩
      have hi_mem : i ∈ Multiset.replicate (b ^ j0) i0 := (Multiset.count_pos).1 hpos
      have hi : i = i0 := (Multiset.mem_replicate).1 hi_mem |>.2
      refine ⟨j0, ?_⟩
      subst hi
      simpa using (Multiset.count_replicate_self i0 (b ^ j0))
  | inr hA =>
      rcases (by simpa [A] using hA) with ⟨i0, rfl⟩
      have hi_mem : i ∈ ({i0} : Multiset (Fin n)) := (Multiset.count_pos).1 hpos
      have hi : i = i0 := (Multiset.mem_singleton).1 hi_mem
      refine ⟨0, ?_⟩
      subst hi
      simpa [pow_zero] using (Multiset.count_singleton_self (a := i0))

theorem macroUnionA_count_pos_unique (n b : ℕ) {m : FreeAbelianMonoid n} :
  m ∈ (MacroSet n b ∪ A n) →
    ∀ {i j : Fin n}, 0 < m.count i → 0 < m.count j → i = j := by
  intro hm
  intro i j hi hj
  rcases hm with hm | hm
  · -- MacroSet case
    rcases hm with ⟨i0, t, ht, rfl⟩
    have hi' : i = i0 := by
      by_contra hne
      have hne' : i0 ≠ i := by
        intro h
        exact hne h.symm
      have hcount : (Multiset.replicate (b ^ t) i0).count i = 0 := by
        simp [Multiset.count_replicate, hne']
      have : (0 : ℕ) < 0 := by
        simpa [hcount] using hi
      exact (lt_irrefl 0) this
    have hj' : j = i0 := by
      by_contra hne
      have hne' : i0 ≠ j := by
        intro h
        exact hne h.symm
      have hcount : (Multiset.replicate (b ^ t) i0).count j = 0 := by
        simp [Multiset.count_replicate, hne']
      have : (0 : ℕ) < 0 := by
        simpa [hcount] using hj
      exact (lt_irrefl 0) this
    exact hi'.trans hj'.symm
  · -- A case
    rcases hm with ⟨i0, rfl⟩
    have hi' : i = i0 := by
      by_contra hne
      have hcount : ({i0} : Multiset (Fin n)).count i = 0 := by
        simpa [Multiset.count_singleton, hne] 
      have : (0 : ℕ) < 0 := by
        simpa [hcount] using hi
      exact (lt_irrefl 0) this
    have hj' : j = i0 := by
      by_contra hne
      have hcount : ({i0} : Multiset (Fin n)).count j = 0 := by
        simpa [Multiset.count_singleton, hne]
      have : (0 : ℕ) < 0 := by
        simpa [hcount] using hj
      exact (lt_irrefl 0) this
    exact hi'.trans hj'.symm

theorem macroUnionA_exists_replicate (n b : ℕ) {m : FreeAbelianMonoid n} :
  m ∈ (MacroSet n b ∪ A n) →
    ∃ i : Fin n, ∃ t : ℕ, m = Multiset.replicate t i := by
  intro hm
  rcases hm with hm | hm
  · rcases hm with ⟨i, j, hj, rfl⟩
    refine ⟨i, b ^ j, rfl⟩
  · rcases hm with ⟨i, rfl⟩
    refine ⟨i, 1, ?_⟩
    simpa using (Multiset.replicate_one i).symm


theorem pow_le_toNat_floor_rpow (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    let β : ℝ := (s : ℝ) / (n * (b - 1))
    let m : ℕ := Int.toNat (Int.floor β)
    b ^ m ≤ ⌊(b : ℝ) ^ β⌋₊ := by
  intro s hs
  dsimp
  set β : ℝ := (s : ℝ) / (n * (b - 1)) with hβ
  set m : ℕ := Int.toNat (Int.floor β) with hm

  -- Step 1: show β ≥ 0 (denominator is positive)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hb1_pos : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℕ) < b := by omega
    have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast this
    exact sub_pos.mpr this
  have hdenom_pos : (0 : ℝ) < (n : ℝ) * ((b : ℝ) - 1) := by
    exact mul_pos hn_pos hb1_pos
  have hβ_nonneg : 0 ≤ β := by
    have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (Nat.zero_le s)
    have hdenom_nonneg : (0 : ℝ) ≤ (n : ℝ) * ((b : ℝ) - 1) := le_of_lt hdenom_pos
    have : (0 : ℝ) ≤ (s : ℝ) / ((n : ℝ) * ((b : ℝ) - 1)) := by
      exact div_nonneg hs_nonneg hdenom_nonneg
    -- rewrite denominator to match β
    simpa [β, hβ, Nat.cast_mul, Nat.cast_sub, hb, Nat.cast_ofNat] using this

  -- Step 2: m is the natural floor of β
  have hm_floor : m = ⌊β⌋₊ := by
    calc
      m = Int.toNat (Int.floor β) := hm
      _ = ⌊β⌋₊ := by
        simpa using (Int.floor_toNat β)

  -- Step 3: floor property gives (m : ℝ) ≤ β
  have hm_le : (m : ℝ) ≤ β := by
    have hfloor_le : (⌊β⌋₊ : ℝ) ≤ β := Nat.floor_le hβ_nonneg
    simpa [hm_floor] using hfloor_le

  -- Step 4: monotonicity of rpow in exponent (base b ≥ 1)
  have hb_real : (1 : ℝ) ≤ (b : ℝ) := by
    have : (1 : ℕ) ≤ b := by omega
    exact_mod_cast this
  have hpow_le : (b : ℝ) ^ (m : ℝ) ≤ (b : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hb_real hm_le

  -- rewrite left side as ((b^m : ℕ) : ℝ)
  have hpow_le' : ((b ^ m : ℕ) : ℝ) ≤ (b : ℝ) ^ β := by
    -- (b:ℝ)^(m:ℝ) = (b:ℝ)^m = ((b^m):ℝ)
    have hb1 : (b : ℝ) ^ (m : ℝ) = (b : ℝ) ^ m := by
      simpa using (Real.rpow_natCast (b : ℝ) m)
    -- now rewrite
    -- avoid simp recursion: use rw step-by-step
    -- first change (b:ℝ)^m to ((b^m):ℝ)
    have hb2 : (b : ℝ) ^ m = ((b ^ m : ℕ) : ℝ) := by
      -- ^ here is Nat.pow on the left (since exponent is Nat)
      -- cast of Nat.pow
      exact (by
        -- `Nat.cast_pow` gives ((b^m):ℝ) = (b:ℝ)^m
        simpa using (Nat.cast_pow b m).symm)
    -- combine
    have : (b : ℝ) ^ (m : ℝ) = ((b ^ m : ℕ) : ℝ) := by
      calc
        (b : ℝ) ^ (m : ℝ) = (b : ℝ) ^ m := hb1
        _ = ((b ^ m : ℕ) : ℝ) := hb2
    -- finish
    -- rewrite the left side of hpow_le
    simpa [this] using hpow_le

  -- Step 5: use Nat.le_floor_iff (need nonnegativity of RHS)
  have hbase_pos : (0 : ℝ) < (b : ℝ) := by
    have : 0 < b := by omega
    exact_mod_cast this
  have hrpow_nonneg : 0 ≤ (b : ℝ) ^ β := by
    exact le_of_lt (Real.rpow_pos_of_pos hbase_pos β)

  exact (Nat.le_floor_iff hrpow_nonneg).2 hpow_le'

theorem r1_le_pow_floor_beta (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    let β : ℝ := (s : ℝ) / (n * (b - 1))
    let k : ℕ := Int.toNat (Int.floor β)
    let r1 : ℕ := Int.toNat (Int.ceil (Real.rpow b (β - 1)))
    r1 ≤ b ^ k := by
  intro s hs
  dsimp
  set β : ℝ := (s : ℝ) / (n * (b - 1))
  set k : ℕ := Int.toNat (Int.floor β)
  set r1 : ℕ := Int.toNat (Int.ceil ((b : ℝ) ^ (β - 1)))

  have hk : k = ⌊β⌋₊ := by
    simpa [k] using (Int.floor_toNat (a := β))

  have hr1 : r1 = ⌈(b : ℝ) ^ (β - 1)⌉₊ := by
    simpa [r1] using (Int.ceil_toNat (a := (b : ℝ) ^ (β - 1)))

  -- Rewrite the goal in terms of Nat.ceil and Nat.floor
  rw [hr1, hk]

  -- It suffices to prove the underlying real inequality
  refine (Nat.ceil_le).2 ?_

  -- show (b:ℝ)^(β-1) ≤ (b ^ ⌊β⌋₊ : ℝ)
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
    have : (1 : ℕ) ≤ b := by omega
    exact_mod_cast this

  -- exponent bound: β - 1 ≤ ⌊β⌋₊
  have h_exp : β - 1 ≤ (⌊β⌋₊ : ℝ) := by
    have hlt : β < (⌊β⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one β)
    linarith

  -- apply monotonicity of rpow in the exponent
  have hpow : (b : ℝ) ^ (β - 1) ≤ (b : ℝ) ^ ((⌊β⌋₊ : ℕ) : ℝ) := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (x := (b : ℝ)) (y := β - 1) (z := (⌊β⌋₊ : ℝ)) hb1 h_exp)

  -- rewrite RHS as (b ^ ⌊β⌋₊ : ℝ)
  -- Real.rpow_natCast : x^(n:ℝ) = x^n
  simpa [Real.rpow_natCast, Nat.cast_pow] using hpow

theorem s_lt_n_mul_beta_succ (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    let β : ℝ := (s : ℝ) / (n * (b - 1))
    let m : ℕ := Int.toNat (Int.floor β)
    (s : ℝ) < (n * (b - 1) * (m + 1) : ℝ) := by
  intro s hs
  dsimp
  set β : ℝ := (s : ℝ) / (n * (b - 1))
  have hβ : β < (⌊β⌋.toNat : ℝ) + 1 := by
    have h : β < (⌊β⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one β)
    simpa [Int.floor_toNat] using h
  have hn : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1)
  have hb' : (0 : ℝ) < (b : ℝ) - 1 := by
    have hb1 : (1 : ℕ) < b := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hb
    have hb1' : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
    simpa using (sub_pos.mpr hb1')
  have hpos : (0 : ℝ) < (n : ℝ) * ((b : ℝ) - 1) := mul_pos hn hb'
  have hmul := (mul_lt_mul_of_pos_left hβ hpos)
  have hne : (n : ℝ) * ((b : ℝ) - 1) ≠ 0 := ne_of_gt hpos
  have hleft : (n : ℝ) * ((b : ℝ) - 1) * β = (s : ℝ) := by
    simpa [β, mul_assoc] using
      (mul_div_cancel_of_imp' (a := (s : ℝ)) (b := (n : ℝ) * ((b : ℝ) - 1)) (by
        intro hb0
        exact (hne hb0).elim))

  -- rewrite the left side using `hleft`
  have hmul' : (s : ℝ) < (n : ℝ) * ((b : ℝ) - 1) * ((⌊β⌋.toNat : ℝ) + 1) := by
    -- `hmul : a*β < a*((⌊β⌋.toNat:ℝ)+1)`
    -- so rewrite `a*β` as `s`
    simpa [hleft] using hmul

  -- rewrite `((⌊β⌋.toNat : ℝ) + 1)` as `((⌊β⌋.toNat + 1 : ℕ) : ℝ)`
  -- and fold the nat multiplication back
  -- goal matches after simp
  simpa [Nat.cast_add, Nat.cast_mul, mul_assoc] using hmul'


theorem sum_filter_lengths_le_length (n b : ℕ) :
  ∀ {L : List (FreeAbelianMonoid n)},
    (∀ m ∈ L, m ∈ (MacroSet n b ∪ A n)) →
    (∑ i : Fin n, (L.filter (fun m => decide (0 < m.count i))).length) ≤ L.length := by
  intro L hL
  induction L with
  | nil =>
      simp
  | cons m L ih =>
      have hm : m ∈ (MacroSet n b ∪ A n) := by
        exact hL m (by simp)
      have htail : ∀ m' ∈ L, m' ∈ (MacroSet n b ∪ A n) := by
        intro m' hm'
        exact hL m' (by simp [hm'])
      have hih :
          (∑ i : Fin n, (L.filter (fun m => decide (0 < m.count i))).length) ≤ L.length :=
        ih htail
      classical

      -- Bound the head element's contribution: at most one index i has 0 < m.count i
      have hsum_card :
          (∑ i : Fin n, (if decide (0 < m.count i) then 1 else 0)) =
            (Finset.univ.filter (fun i : Fin n => 0 < m.count i)).card := by
        simpa [Bool.decide_iff] using
          (Finset.sum_boole (R := Nat)
            (s := (Finset.univ : Finset (Fin n)))
            (p := fun i : Fin n => 0 < m.count i))

      have hcard_le_one :
          (Finset.univ.filter (fun i : Fin n => 0 < m.count i)).card ≤ 1 := by
        have hunique : ∀ {i j : Fin n}, 0 < m.count i → 0 < m.count j → i = j :=
          macroUnionA_count_pos_unique n b (m := m) hm
        refine (Finset.card_le_one_iff).2 ?_
        intro i j hi hj
        have hi' : 0 < m.count i := (Finset.mem_filter.1 hi).2
        have hj' : 0 < m.count j := (Finset.mem_filter.1 hj).2
        exact hunique hi' hj'

      have hhead_sum_le :
          (∑ i : Fin n, (if decide (0 < m.count i) then 1 else 0)) ≤ 1 := by
        simpa [hsum_card] using hcard_le_one

      -- Compute the sum of filter-lengths on (m :: L)
      have hfilter_len :
          ∀ i : Fin n,
            ((m :: L).filter (fun m' => decide (0 < m'.count i))).length =
              (L.filter (fun m' => decide (0 < m'.count i))).length +
                (if decide (0 < m.count i) then 1 else 0) := by
        intro i
        by_cases h : 0 < m.count i
        · simp [List.filter_cons, h, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
        · simp [List.filter_cons, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

      have hsum_len :
          (∑ i : Fin n, ((m :: L).filter (fun m' => decide (0 < m'.count i))).length) =
            (∑ i : Fin n, (L.filter (fun m' => decide (0 < m'.count i))).length) +
              (∑ i : Fin n, (if decide (0 < m.count i) then 1 else 0)) := by
        simp [hfilter_len, Finset.sum_add_distrib, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

      -- Finish by IH + head bound
      calc
        (∑ i : Fin n, ((m :: L).filter (fun m' => decide (0 < m'.count i))).length)
            =
            (∑ i : Fin n, (L.filter (fun m' => decide (0 < m'.count i))).length) +
              (∑ i : Fin n, (if decide (0 < m.count i) then 1 else 0)) :=
          hsum_len
        _ ≤ L.length + 1 := by
          exact Nat.add_le_add hih hhead_sum_le
        _ = (m :: L).length := by
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem sum_map_length_mapIdx_replicate {α : Type*} (g : ℕ → α) :
  ∀ ds : List ℕ,
    (List.map List.length (List.mapIdx (fun j d => List.replicate d (g j)) ds)).sum = ds.sum := by
  intro ds
  induction ds generalizing g with
  | nil =>
      simp
  | cons d ds ih =>
      -- try simp without unfolding mapIdx
      simp [ih (fun j => g (j + 1)), Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


theorem compressList_length (n b : ℕ) (i : Fin n) (x : ℕ) :
  (compressList n b i x).length = (Nat.digits b x).sum := by
  classical
  simpa [compressList, list_length_flatten_eq_sum_lengths] using
    (sum_map_length_mapIdx_replicate (g := fun j => Multiset.replicate (b ^ j) i)
      (ds := Nat.digits b x))


theorem sum_map_sum_mapIdx_replicate {α : Type*} [AddCommMonoid α] (g : ℕ → α) :
  ∀ ds : List ℕ,
    (List.map List.sum (List.mapIdx (fun j d => List.replicate d (g j)) ds)).sum =
      (List.mapIdx (fun j d => d • g j) ds).sum := by
  intro ds
  classical
  -- Rewrite both `mapIdx` into `ofFn`, then use standard `ofFn` lemmas.
  simpa [List.mapIdx_eq_ofFn, List.map_ofFn, List.sum_ofFn, List.sum_replicate, Function.comp]

theorem compressList_sum (n b : ℕ) (i : Fin n) (x : ℕ) :
  (compressList n b i x).sum = Multiset.replicate x i := by
  classical
  -- unfold the definition and turn `sum` of a `flatten` into a sum of sums
  simp [compressList, List.sum_flatten]
  -- use the provided axiom about sums of `replicate` blocks
  rw [sum_map_sum_mapIdx_replicate
        (g := fun j => Multiset.replicate (b ^ j) i)
        (ds := b.digits x)]
  set ds : List ℕ := b.digits x with hds
  -- rewrite each scalar multiple of a replicate as one scalar multiple of a singleton
  have hscalar : ∀ j d : ℕ,
      d • Multiset.replicate (b ^ j) i = (d * b ^ j) • ({i} : Multiset (Fin n)) := by
    intro j d
    -- `Multiset.replicate t i = t • {i}`
    rw [(Multiset.nsmul_singleton i (b ^ j)).symm]
    -- reassociate the two `nsmul`s
    simpa using (mul_nsmul' ({i} : Multiset (Fin n)) d (b ^ j)).symm
  have hlist :
      ds.mapIdx (fun j d => d • Multiset.replicate (b ^ j) i) =
        ds.mapIdx (fun j d => (d * b ^ j) • ({i} : Multiset (Fin n))) := by
    rw [List.mapIdx_eq_ofFn ds (fun j d => d • Multiset.replicate (b ^ j) i)]
    rw [List.mapIdx_eq_ofFn ds (fun j d => (d * b ^ j) • ({i} : Multiset (Fin n)))]
    refine congrArg List.ofFn ?_
    funext k
    simpa using (hscalar (j := (k : ℕ)) (d := ds.get k))
  have hcomp :
      ds.mapIdx (fun j d => (d * b ^ j) • ({i} : Multiset (Fin n))) =
        (ds.mapIdx (fun j d => d * b ^ j)).map
          (fun t : ℕ => t • ({i} : Multiset (Fin n))) := by
    rw [List.mapIdx_eq_ofFn ds (fun j d => (d * b ^ j) • ({i} : Multiset (Fin n)))]
    rw [List.mapIdx_eq_ofFn ds (fun j d => d * b ^ j)]
    -- rewrite RHS `map` of `ofFn`
    rw [List.map_ofFn
        (f := fun k : Fin ds.length => (fun j d => d * b ^ j) (k : ℕ) (ds.get k))
        (g := fun t : ℕ => t • ({i} : Multiset (Fin n)))]
    rfl
  rw [hlist]
  rw [hcomp]
  rw [list_sum_map_multiset_replicate
        (a := ({i} : Multiset (Fin n)))
        (l := ds.mapIdx (fun j d => d * b ^ j))]
  have hx : (ds.mapIdx (fun j d => d * b ^ j)).sum = x := by
    have h1 : (ds.mapIdx (fun j d => d * b ^ j)).sum = Nat.ofDigits b ds := by
      simpa using (Nat.ofDigits_eq_sum_mapIdx b ds).symm
    have h2 : Nat.ofDigits b ds = x := by
      simpa [hds] using (Nat.ofDigits_digits b x)
    exact h1.trans h2
  rw [hx]
  -- convert back from scalar multiple of a singleton to `Multiset.replicate`
  simpa using (Multiset.nsmul_singleton i x)


theorem compress_replicate_of_le_pow (n b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) (i : Fin n) (x : ℕ) :
  x ≤ b ^ k →
    ∃ l : List (FreeAbelianMonoid n),
      l.length ≤ (b - 1) * k ∧
      (∀ m ∈ l, m ∈ (MacroSet n b ∪ A n)) ∧
      l.sum = Multiset.replicate x i := by
  intro hx
  refine ⟨compressList n b i x, ?_, ?_, ?_⟩
  ·
    have hsumle : (Nat.digits b x).sum ≤ (b - 1) * k :=
      digits_sum_le_of_le_pow b k x hb hk hx
    simpa [compressList_length] using hsumle
  ·
    exact compressList_mem n b i x
  ·
    exact compressList_sum n b i x


theorem macroSet_ball_inclusion_pow (n b k : ℕ) (hb : 2 ≤ b) (hk : 1 ≤ k) :
  Ball (b ^ k) (A n) ⊆ Ball (n * (b - 1) * k) (MacroSet n b ∪ A n) := by
  classical
  intro m hm
  have hcard : m.card ≤ b ^ k := (ball_A_mem_iff_card_le (n := n) (R := b ^ k) m).1 hm
  have hcount : ∀ i : Fin n, m.count i ≤ b ^ k := by
    intro i
    exact le_trans (Multiset.count_le_card i m) hcard
  let lfun : Fin n → List (FreeAbelianMonoid n) := fun i =>
    Classical.choose
      (compress_replicate_of_le_pow n b k hb hk i (m.count i) (hcount i))
  have hfun_len : ∀ i : Fin n, (lfun i).length ≤ (b - 1) * k := by
    intro i
    simpa [lfun] using
      (Classical.choose_spec
        (compress_replicate_of_le_pow n b k hb hk i (m.count i) (hcount i))).1
  have hfun_mem : ∀ i : Fin n, ∀ mm : FreeAbelianMonoid n, mm ∈ lfun i → mm ∈ (MacroSet n b ∪ A n) := by
    intro i mm hmm
    have :=
      (Classical.choose_spec
        (compress_replicate_of_le_pow n b k hb hk i (m.count i) (hcount i))).2.1
    exact this mm hmm
  have hfun_sum : ∀ i : Fin n, (lfun i).sum = Multiset.replicate (m.count i) i := by
    intro i
    simpa [lfun] using
      (Classical.choose_spec
        (compress_replicate_of_le_pow n b k hb hk i (m.count i) (hcount i))).2.2
  let L : List (FreeAbelianMonoid n) := (List.ofFn lfun).flatten
  refine ⟨L, ?_, ?_, ?_⟩
  ·
    -- length bound
    have hlen_flat : ((List.ofFn lfun).flatten).length = ((List.ofFn lfun).map List.length).sum := by
      simpa using (List.length_flatten (L := List.ofFn lfun))
    have hlen_flat' : L.length = ((List.ofFn lfun).map List.length).sum := by
      simpa [L] using hlen_flat
    have hmap : (List.ofFn lfun).map List.length = List.ofFn (List.length ∘ lfun) := by
      simpa using (List.map_ofFn lfun List.length)
    have hlen_eq : L.length = (List.ofFn (List.length ∘ lfun)).sum := by
      simpa [hmap] using hlen_flat'
    have hsum_eq : (List.ofFn (List.length ∘ lfun)).sum = ∑ i : Fin n, List.length (lfun i) := by
      simpa [Function.comp] using (List.sum_ofFn (f := fun i : Fin n => List.length (lfun i)))
    have hbound : (∑ i : Fin n, List.length (lfun i)) ≤ ∑ i : Fin n, (b - 1) * k := by
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i hi => hfun_len i))
    calc
      L.length = ∑ i : Fin n, List.length (lfun i) := Eq.trans hlen_eq hsum_eq
      _ ≤ ∑ i : Fin n, (b - 1) * k := hbound
      _ = n * ((b - 1) * k) := by
        simpa using (Fin.sum_const (n := n) ((b - 1) * k))
      _ = n * (b - 1) * k := by
        simpa [Nat.mul_assoc] using (Nat.mul_assoc n (b - 1) k).symm
  ·
    -- membership
    intro x hx
    have hx' : x ∈ (List.ofFn lfun).flatten := by
      simpa only [L] using hx
    rcases (List.mem_flatten.mp hx') with ⟨t, ht, hxt⟩
    rcases (List.mem_ofFn' lfun t).1 ht with ⟨i, rfl⟩
    exact hfun_mem i x hxt
  ·
    -- sum
    have hsum_flat : L.sum = ((List.ofFn lfun).map List.sum).sum := by
      simpa [L] using (List.sum_flatten (l := List.ofFn lfun))
    have hmap' : (List.ofFn lfun).map List.sum = List.ofFn (List.sum ∘ lfun) := by
      simpa using (List.map_ofFn lfun List.sum)
    have hsum1 : L.sum = (List.ofFn (List.sum ∘ lfun)).sum := by
      simpa [hsum_flat, hmap']
    have hsum2 : (List.ofFn (List.sum ∘ lfun)).sum = ∑ i : Fin n, (lfun i).sum := by
      simpa [Function.comp] using (List.sum_ofFn (f := fun i : Fin n => (lfun i).sum))
    have hsum3 : L.sum = ∑ i : Fin n, Multiset.replicate (m.count i) i := by
      -- rewrite using hfun_sum
      calc
        L.sum = ∑ i : Fin n, (lfun i).sum := by
          exact Eq.trans hsum1 hsum2
        _ = ∑ i : Fin n, Multiset.replicate (m.count i) i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hfun_sum i
    have hdecomp : (∑ i : Fin n, Multiset.replicate (m.count i) i) = m := by
      ext a
      calc
        Multiset.count a (∑ i : Fin n, Multiset.replicate (m.count i) i)
            = ∑ i : Fin n, Multiset.count a (Multiset.replicate (m.count i) i) := by
              simpa using
                (Multiset.count_sum' (s := (Finset.univ : Finset (Fin n))) (a := a)
                  (f := fun i : Fin n => Multiset.replicate (m.count i) i))
        _ = ∑ i : Fin n, (if i = a then m.count i else 0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [Multiset.count_replicate, eq_comm]
        _ = m.count a := by
              simpa using (Fintype.sum_ite_eq (a := a) (f := fun i : Fin n => m.count i))
    calc
      L.sum = ∑ i : Fin n, Multiset.replicate (m.count i) i := hsum3
      _ = m := hdecomp


theorem macroSet_ball_inclusion_r1 (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
    Ball r1 (A n) ⊆ Ball s ((MacroSet n b) ∪ (A n)) := by
  intro s hs
  dsimp
  set r1 : ℕ := Int.toNat (Int.ceil (Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1))) with hr1
  let β : ℝ := (s : ℝ) / (n * (b - 1))
  let k : ℕ := Int.toNat (Int.floor β)
  have hr1_eq : r1 = Int.toNat (Int.ceil (Real.rpow b (β - 1))) := by
    simpa [β] using hr1
  have hr1_le_pow : r1 ≤ b ^ k := by
    have h : Int.toNat (Int.ceil (Real.rpow b (β - 1))) ≤ b ^ k := by
      simpa [β, k] using r1_le_pow_floor_beta n b h1 hb s hs
    simpa [hr1_eq] using h
  by_cases hk0 : k = 0
  · have hr1_le_s : r1 ≤ s := by
      have hr1_le_one : r1 ≤ 1 := by
        simpa [hk0] using hr1_le_pow
      exact le_trans hr1_le_one hs
    have hA_subset : (A n : Set (FreeAbelianMonoid n)) ⊆ MacroSet n b ∪ A n := by
      intro m hm
      exact Or.inr hm
    have hBall_rad : Ball r1 (A n) ⊆ Ball s (A n) :=
      ball_mono_radius (n := n) (R := r1) (S := s) (X := A n) hr1_le_s
    have hBall_set : Ball s (A n) ⊆ Ball s (MacroSet n b ∪ A n) :=
      ball_mono_set (n := n) (R := s) (X := A n) (Y := MacroSet n b ∪ A n) hA_subset
    exact hBall_rad.trans hBall_set
  · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    have hBall_r1_pow : Ball r1 (A n) ⊆ Ball (b ^ k) (A n) :=
      ball_mono_radius (n := n) (R := r1) (S := b ^ k) (X := A n) hr1_le_pow
    have hBall_pow :
        Ball (b ^ k) (A n) ⊆ Ball (n * (b - 1) * k) (MacroSet n b ∪ A n) :=
      macroSet_ball_inclusion_pow n b k hb hk
    have hmul_le_s : n * (b - 1) * k ≤ s := by
      simpa [β, k] using floor_beta_mul_le_s n b h1 hb s hs
    have hBall_mul :
        Ball (n * (b - 1) * k) (MacroSet n b ∪ A n) ⊆ Ball s (MacroSet n b ∪ A n) :=
      ball_mono_radius (n := n) (R := n * (b - 1) * k) (S := s)
        (X := MacroSet n b ∪ A n) hmul_le_s
    exact hBall_r1_pow.trans (hBall_pow.trans hBall_mul)

theorem sum_pows_len_ge_pow_sub_one (b k : ℕ) (hb : 2 ≤ b) :
  ∀ l : List ℕ,
    (∀ x ∈ l, ∃ j : ℕ, x = b ^ j) →
    l.sum = b ^ k - 1 →
    (b - 1) * k ≤ l.length := by
  classical
  induction k with
  | zero =>
      intro l hl hsum
      simpa using (Nat.zero_le l.length)
  | succ k ih =>
      intro l hl hsum
      -- Split `l` into the `1`'s and the non-`1`'s
      let l0 : List ℕ := l.filter fun x => x = 1
      let l1 : List ℕ := l.filter fun x => x ≠ 1
      have hlen : l.length = l0.length + l1.length := by
        simpa [l0, l1] using
          (List.length_eq_length_filter_add (l := l) (f := fun x => decide (x = (1 : ℕ))))
      -- Sum also splits
      have hsum_split : l0.sum + l1.sum = l.sum := by
        simpa [l0, l1] using
          (List.sum_map_filter_add_sum_map_filter_not (p := fun x : ℕ => x = 1) (f := fun x : ℕ => x) l)
      -- `l0` consists only of `1`'s, so its sum is its length.
      have hl0 : ∀ x ∈ l0, x = (1 : ℕ) := by
        intro x hx
        have hx' : x ∈ l ∧ x = 1 := by
          simpa [l0] using (List.mem_filter.mp hx)
        exact hx'.2
      have hsum_l0 : l0.sum = l0.length := by
        simpa using (List.sum_eq_card_nsmul (l := l0) (m := (1 : ℕ)) hl0)
      -- Every element of `l1` is divisible by `b`.
      have hl1_dvd : ∀ x ∈ l1, b ∣ x := by
        intro x hx
        have hx' : x ∈ l ∧ x ≠ 1 := by
          simpa [l1] using (List.mem_filter.mp hx)
        rcases hl x hx'.1 with ⟨j, rfl⟩
        cases j with
        | zero =>
            cases hx'.2 (by simp)
        | succ j =>
            -- `b ∣ b^(j+1)`
            simpa [Nat.pow_succ] using dvd_mul_of_dvd_right (dvd_refl b) (b ^ j)
      have hb0 : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
      have hdiv_l1 : b ∣ l1.sum := by
        exact List.dvd_sum (a := b) (l := l1) hl1_dvd
      -- The sum modulo `b` is determined by the `1`'s.
      have hmod : l.sum % b = l0.length % b := by
        have hl1mod : l1.sum % b = 0 := Nat.mod_eq_zero_of_dvd hdiv_l1
        -- use `l.sum = l0.sum + l1.sum`
        calc
          l.sum % b = (l0.sum + l1.sum) % b := by simpa [hsum_split]
          _ = (l0.sum % b + l1.sum % b) % b := by simp [Nat.add_mod]
          _ = l0.length % b := by simp [hl1mod, hsum_l0]
      -- compute the remainder of `b^(k+1)-1` mod `b`
      have hrem : (b ^ k.succ - 1) % b = b - 1 := by
        have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
        have hb_lt : b - 1 < b := by
          omega
        -- `b^k.succ ≡ b (mod b)`
        have hpow_dvd : b ∣ b ^ k.succ := by
          -- `b^k.succ = b^k * b`
          simpa [Nat.pow_succ] using dvd_mul_of_dvd_right (dvd_refl b) (b ^ k)
        have hpow0 : b ^ k.succ ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).2 hpow_dvd
        have hb0' : b ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).2 (dvd_refl b)
        have hab : b ^ k.succ ≡ b [MOD b] := hpow0.trans hb0'.symm
        have hsub : b ^ k.succ - 1 ≡ b - 1 [MOD b] :=
          Nat.ModEq.sub (by
            -- `1 ≤ b^k.succ`
            have : 0 < b ^ k.succ := Nat.pow_pos hb0
            exact (Nat.succ_le_iff).2 this
          ) hb1 hab (Nat.ModEq.rfl)
        exact Nat.mod_eq_of_modEq hsub hb_lt
      -- The number of `1`'s has remainder `b-1` modulo `b`.
      have hc0mod : l0.length % b = b - 1 := by
        have hsum_mod : l.sum % b = b - 1 := by
          calc
            l.sum % b = (b ^ k.succ - 1) % b := by simpa [hsum]
            _ = b - 1 := hrem
        simpa [hmod] using hsum_mod
      -- Define the quotient `q` of the number of `1`'s by `b`.
      let q : ℕ := l0.length / b
      -- Express `l0.length` in terms of quotient and remainder.
      have hc0 : l0.length = (b - 1) + b * q := by
        have hdivalg : l0.length = l0.length % b + b * (l0.length / b) := by
          simpa using (Nat.mod_add_div l0.length b).symm
        -- simplify using `hc0mod`
        simpa [q, hc0mod, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdivalg
      -- Build the reduced list for the induction hypothesis
      let l' : List ℕ := List.replicate q 1 ++ l1.map (fun x => x / b)
      have hl'pow : ∀ x ∈ l', ∃ j : ℕ, x = b ^ j := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · -- from the replicate part
          have hx1 : x = 1 := (List.mem_replicate.mp hx).2
          refine ⟨0, ?_⟩
          simpa [hx1]
        · -- from the mapped part
          rcases List.mem_map.mp hx with ⟨y, hy1, rfl⟩
          have hy' : y ∈ l ∧ y ≠ 1 := by
            simpa [l1] using (List.mem_filter.mp hy1)
          rcases hl y hy'.1 with ⟨j, rfl⟩
          cases j with
          | zero =>
              cases hy'.2 (by simp)
          | succ j =>
              refine ⟨j, ?_⟩
              -- `b^(j+1) / b = b^j`
              have : (b * b ^ j) / b = b ^ j := Nat.mul_div_right (b ^ j) hb0
              -- rewrite `b^(j+1)` as `b * b^j`
              simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
      -- compute the sum of `l1.map (· / b)`
      have hsum_div : (l1.map (fun x => x / b)).sum = l1.sum / b := by
        -- prove a general lemma by induction on the list
        have hgen : ∀ t : List ℕ, (∀ x ∈ t, b ∣ x) → (t.map (fun x => x / b)).sum = t.sum / b := by
          intro t ht
          induction t with
          | nil => simp
          | cons a t ih =>
              have ha : b ∣ a := ht a (by simp)
              have ht' : ∀ x ∈ t, b ∣ x := by
                intro x hx
                exact ht x (by simp [hx])
              simp [List.sum_cons, ih ht', Nat.add_div_of_dvd_right ha]
        exact hgen l1 hl1_dvd
      -- show `l'.sum = b^k - 1`
      have hsum_l' : l'.sum = b ^ k - 1 := by
        -- First, rewrite `l0.length + l1.sum = b^(k+1)-1`.
        have hsum_eq : l0.length + l1.sum = b ^ k.succ - 1 := by
          simpa [hsum_l0, hsum] using hsum_split
        -- We show `q + l1.sum / b = b^k - 1`.
        have hq_eq : q + l1.sum / b = b ^ k - 1 := by
          have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
          -- substitute `hc0`
          have h1 : (b - 1) + b * q + l1.sum = b ^ k.succ - 1 := by
            simpa [hc0, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum_eq
          -- subtract `b-1`
          have h2 : b * q + l1.sum = b ^ k.succ - 1 - (b - 1) := by
            have h1' : (b - 1) + (b * q + l1.sum) = b ^ k.succ - 1 := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h1
            have hsub := congrArg (fun t => t - (b - 1)) h1'
            -- simplify
            simpa [Nat.add_sub_cancel] using hsub
          -- divide by `b`
          have h2div := congrArg (fun t => t / b) h2
          -- simplify LHS
          have hleft : (b * q + l1.sum) / b = q + l1.sum / b := by
            have hadd : (b * q + l1.sum) / b = (b * q) / b + l1.sum / b :=
              Nat.add_div_of_dvd_left (a := b * q) (b := l1.sum) (c := b) hdiv_l1
            have hmul : (b * q) / b = q := Nat.mul_div_right q hb0
            simpa [hadd, hmul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          -- simplify RHS
          have hright : (b ^ k.succ - 1 - (b - 1)) / b = b ^ k - 1 := by
            have hb1' : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
            have hbpos : 0 < b := hb0
            have h_one : 1 + (b - 1) = b := by
              -- `b - 1 + 1 = b`
              have := Nat.sub_add_cancel hb1'
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
            have hrewrite : b ^ k.succ - 1 - (b - 1) = b * (b ^ k - 1) := by
              calc
                b ^ k.succ - 1 - (b - 1)
                    = b ^ k.succ - (1 + (b - 1)) := by
                        simpa [Nat.sub_sub]
                _ = b ^ k.succ - b := by simpa [h_one]
                _ = b * (b ^ k - 1) := by
                      -- `b^(k+1) - b = b*(b^k - 1)`
                      calc
                        b ^ k.succ - b = b ^ k * b - b := by simp [Nat.pow_succ]
                        _ = b * b ^ k - b := by
                              -- commute the product
                              simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
                        _ = b * (b ^ k - 1) := by
                              simpa using (mul_tsub_one b (b ^ k)).symm
            calc
              (b ^ k.succ - 1 - (b - 1)) / b
                  = (b * (b ^ k - 1)) / b := by simpa [hrewrite]
              _ = b ^ k - 1 := by simpa using Nat.mul_div_right (b ^ k - 1) hbpos
          -- conclude
          have := congrArg (fun t => t) h2div
          -- rewrite both sides
          simpa [hleft, hright] using h2div
        -- Now compute `l'.sum`
        -- `sum(replicate q 1) = q`
        simp [l', hq_eq, hsum_div, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      -- Apply the induction hypothesis to `l'`.
      have hlen_l' : (b - 1) * k ≤ l'.length := ih l' hl'pow hsum_l'
      -- Relate `l'.length` and `l.length`.
      have hlen_rel : (b - 1) + l'.length ≤ l.length := by
        -- `l'.length = q + l1.length`
        have hl'len : l'.length = q + l1.length := by
          simp [l']
        -- `l.length = l0.length + l1.length = (b-1) + b*q + l1.length`
        have hl_len : l.length = (b - 1) + b * q + l1.length := by
          -- from `hlen` and `hc0`
          calc
            l.length = l0.length + l1.length := hlen
            _ = ((b - 1) + b * q) + l1.length := by simpa [hc0]
            _ = (b - 1) + b * q + l1.length := by omega
        -- use `q ≤ b*q` to bound
        have hb1 : 1 ≤ b := le_trans (by decide : 1 ≤ 2) hb
        have hbq : q ≤ b * q := by
          simpa [Nat.one_mul] using (Nat.mul_le_mul_right q hb1)
        have : (b - 1) + (q + l1.length) ≤ (b - 1) + (b * q + l1.length) := by
          exact Nat.add_le_add_left (Nat.add_le_add_right hbq _) _
        simpa [hl'len, hl_len, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      -- Finish.
      have : (b - 1) * k.succ ≤ l.length := by
        have : (b - 1) + (b - 1) * k ≤ (b - 1) + l'.length :=
          Nat.add_le_add_left hlen_l' (b - 1)
        have : (b - 1) + (b - 1) * k ≤ l.length := le_trans this hlen_rel
        simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      simpa using this

theorem hardElement_coord_filter_len (n b k : ℕ) (hb : 2 ≤ b) (i : Fin n) :
  ∀ {L : List (FreeAbelianMonoid n)},
    (∀ m ∈ L, m ∈ (MacroSet n b ∪ A n)) →
    L.sum = hardElement n b k →
    (b - 1) * k ≤ (L.filter (fun m => decide (0 < m.count i))).length := by
  intro L hLmem hsum
  classical
  let Li : List (FreeAbelianMonoid n) :=
    L.filter (fun m => decide (0 < m.count i))
  let ci : List ℕ := Li.map (fun m => m.count i)

  have hpow : ∀ x ∈ ci, ∃ j : ℕ, x = b ^ j := by
    intro x hx
    rcases List.mem_map.1 hx with ⟨m, hmLi, rfl⟩
    have hm : m ∈ L ∧ decide (0 < m.count i) = true := by
      simpa [Li] using (List.mem_filter.1 hmLi)
    have hmMacro : m ∈ (MacroSet n b ∪ A n) := hLmem m hm.1
    have hpos : 0 < m.count i := (Bool.decide_iff _).1 hm.2
    exact macroUnionA_count_pos_pow n b hb hmMacro hpos

  have hsumAll : (L.map (fun m : FreeAbelianMonoid n => m.count i)).sum = b ^ k - 1 := by
    have hcount : (Multiset.countAddMonoidHom i) (L.sum) =
        (Multiset.countAddMonoidHom i) (hardElement n b k) := by
      simpa using
        congrArg (fun m : FreeAbelianMonoid n => (Multiset.countAddMonoidHom i) m) hsum
    have hcount' : (L.map (Multiset.countAddMonoidHom i)).sum =
        (Multiset.countAddMonoidHom i) (hardElement n b k) := by
      calc
        (L.map (Multiset.countAddMonoidHom i)).sum =
            (Multiset.countAddMonoidHom i) (L.sum) := by
              simpa using (map_list_sum (Multiset.countAddMonoidHom i) L).symm
        _ = (Multiset.countAddMonoidHom i) (hardElement n b k) := by
              simpa using hcount
    have hcount'' : (L.map (fun m : FreeAbelianMonoid n => m.count i)).sum =
        (hardElement n b k).count i := by
      simpa [Multiset.coe_countAddMonoidHom] using hcount'
    simpa [hardElement_count] using hcount''

  have hsum_filter :
      (L.map (fun m : FreeAbelianMonoid n => if 0 < m.count i then m.count i else 0)).sum =
        ci.sum := by
    -- use List.sum_map_ite with g = 0
    have h :=
      (List.sum_map_ite (p := fun m : FreeAbelianMonoid n => 0 < m.count i)
        (f := fun m : FreeAbelianMonoid n => m.count i) (g := fun _ => (0 : ℕ)) (l := L))
    -- simplify the right-hand side
    --
    -- Goal: conditional sum = ci.sum
    --
    simpa [Li, ci] using h

  have hfun :
      (fun m : FreeAbelianMonoid n => if 0 < m.count i then m.count i else 0) =
        (fun m : FreeAbelianMonoid n => m.count i) := by
    funext m
    by_cases hm : 0 < m.count i
    · simp [hm]
    · have hm0 : m.count i = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt hm)
      simp [hm, hm0]

  have hsumci : ci.sum = b ^ k - 1 := by
    -- relate ci.sum to sum over all counts
    have hci_eq : ci.sum = (L.map (fun m : FreeAbelianMonoid n => m.count i)).sum := by
      -- from hsum_filter and hfun
      have hcond :
          (L.map (fun m : FreeAbelianMonoid n => if 0 < m.count i then m.count i else 0)).sum =
            (L.map (fun m : FreeAbelianMonoid n => m.count i)).sum := by
        simpa [hfun]
      -- combine
      calc
        ci.sum =
            (L.map (fun m : FreeAbelianMonoid n => if 0 < m.count i then m.count i else 0)).sum :=
              by simpa using hsum_filter.symm
        _ = (L.map (fun m : FreeAbelianMonoid n => m.count i)).sum := hcond
    -- finish
    simpa [hci_eq] using hsumAll

  have hlen : (b - 1) * k ≤ ci.length :=
    sum_pows_len_ge_pow_sub_one b k hb ci hpow hsumci

  -- lengths: map preserves length
  -- and Li is the desired filter
  simpa [Li, ci] using hlen

theorem hardElement_min_length (n b k : ℕ) (hb : 2 ≤ b) :
  ∀ {L : List (FreeAbelianMonoid n)},
    (∀ m ∈ L, m ∈ (MacroSet n b ∪ A n)) →
    L.sum = hardElement n b k →
    n * (b - 1) * k ≤ L.length := by
  intro L hL hsum
  classical
  have hcoord : ∀ i : Fin n,
      (b - 1) * k ≤ (L.filter (fun m => decide (0 < m.count i))).length := by
    intro i
    exact hardElement_coord_filter_len n b k hb i (L := L) hL hsum
  have hsum_coord :
      (Finset.univ.sum (fun i : Fin n => (b - 1) * k))
        ≤ Finset.univ.sum
            (fun i : Fin n => (L.filter (fun m => decide (0 < m.count i))).length) := by
    classical
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hcoord i
  have hfilter :
      (Finset.univ.sum
            (fun i : Fin n => (L.filter (fun m => decide (0 < m.count i))).length))
        ≤ L.length := by
    simpa using (sum_filter_lengths_le_length n b (L := L) hL)
  have hmain : n * ((b - 1) * k) ≤ L.length := by
    have h1 : n * ((b - 1) * k)
        ≤ Finset.univ.sum
            (fun i : Fin n => (L.filter (fun m => decide (0 < m.count i))).length) := by
      simpa using hsum_coord
    exact le_trans h1 hfilter
  simpa [Nat.mul_assoc] using hmain


theorem macroSet_ball_not_inclusion_r2 (n b : ℕ) (h1 : 1 ≤ n) (hb : 2 ≤ b) :
  ∀ s : ℕ, s ≥ 1 →
    let r2 := 1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (b - 1))))
    ¬ (Ball r2 (A n) ⊆ Ball s ((MacroSet n b) ∪ (A n))) := by
  classical
  intro s hs
  dsimp
  let β : ℝ := (s : ℝ) / (n * (b - 1))
  let m : ℕ := Int.toNat (Int.floor β)
  let k : ℕ := m + 1
  let p : ℕ := Int.toNat (Int.floor (Real.rpow b β))
  let w : FreeAbelianMonoid n := hardElement n b k
  have hw_ballA : w ∈ Ball (1 + n * b * p) (A n) := by
    have hpow : b ^ m ≤ p := by
      have h := pow_le_toNat_floor_rpow (n := n) (b := b) h1 hb s hs
      simpa [β, m, p] using h
    have hbkp : b ^ k ≤ b * p := by
      have := Nat.mul_le_mul_left b hpow
      simpa [k, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    have hsub : b ^ k - 1 ≤ b * p := by
      exact le_trans (Nat.sub_le (b ^ k) 1) hbkp
    have hcard_le : w.card ≤ 1 + n * b * p := by
      have hwcard : w.card = n * (b ^ k - 1) := by
        simpa [w] using hardElement_card n b k
      have hn : n * (b ^ k - 1) ≤ n * (b * p) := Nat.mul_le_mul_left n hsub
      rw [hwcard]
      have hx : n * b * p ≤ 1 + n * b * p := by
        have hx' : n * b * p ≤ n * b * p + 1 := Nat.le_succ _
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx'
      calc
        n * (b ^ k - 1) ≤ n * (b * p) := hn
        _ = n * b * p := by
          simp [Nat.mul_assoc]
        _ ≤ 1 + n * b * p := hx
    exact (ball_A_mem_iff_card_le (n := n) (R := 1 + n * b * p) (m := w)).2 hcard_le
  have hw_not_ballMacro : w ∉ Ball s (MacroSet n b ∪ A n) := by
    intro hw
    rcases hw with ⟨L, hLlen, hLmem, hLsum⟩
    have hmin : n * (b - 1) * k ≤ L.length := by
      have hmem' : ∀ m' ∈ L, m' ∈ MacroSet n b ∪ A n := by
        intro m' hm'
        exact hLmem m' hm'
      exact hardElement_min_length n b k hb (L := L) (by
        intro m' hm'
        exact hmem' m' hm') hLsum
    have hNk_le_s : n * (b - 1) * k ≤ s := le_trans hmin hLlen
    have hNk_le_sR : ((n * (b - 1) * k : ℕ) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hNk_le_s
    have hslt : (s : ℝ) < ((n * (b - 1) * k : ℕ) : ℝ) := by
      have h := s_lt_n_mul_beta_succ (n := n) (b := b) h1 hb s hs
      have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hb
      simpa [β, m, k, mul_assoc, Nat.cast_pred hbpos] using h
    exact (not_lt_of_ge hNk_le_sR) hslt
  intro hinc
  have : w ∈ Ball s (MacroSet n b ∪ A n) := hinc hw_ballA
  exact hw_not_ballMacro this

theorem theorem_1_place_notation_exponential_expansion (n b : ℕ)
  (h1 : 1 ≤ n)
  (hb : 2 ≤ b) :
  let M := MacroSet n b
  (∃ (d1 d2 : Real), ∀ (x : ℕ), (x ≥ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log x) ≤ (M ∩ (Ball x (A n))).ncard
      ∧ (M ∩ (Ball x (A n))).ncard ≤ d2 * (Real.log x))
    ∧
    ∀ s : ℕ, s ≥ 1 → (
      let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
      (Ball r1 (A n) ⊆ (Ball s (M ∪ (A n))))
      ∧
      let r2 := 1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (b - 1))))
      ¬ (Ball r2 (A n) ⊆ (Ball s (M ∪ (A n))))) := by
  classical
  simp
  constructor
  · exact macroSet_log_density n b h1 hb
  · intro s hs
    constructor
    · simpa using (macroSet_ball_inclusion_r1 n b h1 hb s hs)
    · simpa using (macroSet_ball_not_inclusion_r2 n b h1 hb s hs)



theorem theorem_2_quasi_exponential_expansion
  (n : ℕ)
  (h1 : 1 ≤ n)
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

def IsThetaFromOne (f g : ℕ → ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ,
    0 < C₁ ∧ 0 < C₂ ∧
    ∀ s : ℕ, 1 ≤ s → C₁ * g s ≤ f s ∧ f s ≤ C₂ * g s

-- theorem theorem_4_double_logarithmic
--   (b: ℕ)


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
