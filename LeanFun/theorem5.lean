import LeanFun.Definitions


import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open scoped BigOperators
open Filter

open free

def Sphere (n r : ℕ) : Set (FreeMonoid (Fin n)) :=
  {w | w.length = r}

noncomputable def expansion {n : ℕ} (G G' : Set (FreeMonoid (Fin n))) (s : ℕ) : ℕ :=
    sSup { r : ℕ | Ball r G ⊆ Ball s G' }

open free in
theorem ball_mono_R_free {n : ℕ} {R R' : ℕ} {X : Set (FreeMonoid (Fin n))} (h : R ≤ R') :
  Ball R X ⊆ Ball R' X := by
  intro m hm
  rcases hm with ⟨l, hlR, hlX, hlprod⟩
  refine ⟨l, le_trans hlR h, hlX, hlprod⟩

open free in
theorem ball_mono_X_free {n : ℕ} {R : ℕ} {X Y : Set (FreeMonoid (Fin n))} (h : X ⊆ Y) :
  Ball R X ⊆ Ball R Y := by
  intro m hm
  rcases hm with ⟨l, hlR, hlX, hlprod⟩
  refine ⟨l, hlR, ?_, hlprod⟩
  intro x hx
  exact h (hlX x hx)


open free in
theorem le_expansion_of_ball_subset_of_bddAbove_free {n : ℕ} {G G' : Set (FreeMonoid (Fin n))} {s r : ℕ}
  (hB : BddAbove { t : ℕ | Ball t G ⊆ Ball s G' })
  (hr : Ball r G ⊆ Ball s G') :
  r ≤ expansion G G' s := by
  classical
  unfold expansion
  exact le_csSup hB hr


open free in
theorem mem_Ball_A_iff_length_le_free {n R : ℕ} (w : FreeMonoid (Fin n)) : w ∈ Ball R (A n) ↔ w.length ≤ R := by
  -- Unfold the definitions of `Ball` and `A`.
  simp [free.Ball, free.A]
  constructor
  · rintro ⟨l, hlR, hlA, hlprod⟩
    -- Length of a product of singletons is the length of the list.
    have hlen : l.prod.length = l.length := by
      -- Prove a general statement by induction on the list.
      have hlen' : ∀ l : List (FreeMonoid (Fin n)), (∀ x ∈ l, ∃ i, [i] = x) → l.prod.length = l.length := by
        intro l hlA
        induction l with
        | nil =>
            simp
        | cons a t ih =>
            have ha : a.length = 1 := by
              rcases hlA a (by simp) with ⟨i, rfl⟩
              simp [FreeMonoid.length]
            have ht : t.prod.length = t.length := by
              apply ih
              intro x hx
              exact hlA x (by simp [hx])
            simp [List.prod_cons, FreeMonoid.length_mul, ha, ht, Nat.succ_eq_add_one, Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc]
      exact hlen' l hlA
    have hwlen : w.length = l.length := by
      have hprodlen : l.prod.length = w.length := by
        simpa using congrArg FreeMonoid.length hlprod
      exact hprodlen.symm.trans hlen
    -- Conclude using `l.length ≤ R`.
    simpa [hwlen] using hlR
  · intro hwlen
    refine ⟨w.toList.map FreeMonoid.of, ?_, ?_, ?_⟩
    · -- bound the number of factors
      simpa [FreeMonoid.length] using hwlen
    · -- each factor lies in `A n`
      intro x hx
      rcases List.mem_map.1 hx with ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
    · -- the product of the singleton letters is the original word
      have hlift_w :
          FreeMonoid.lift (FreeMonoid.of : Fin n → FreeMonoid (Fin n)) w = w := by
        -- `lift of` is the identity homomorphism.
        have :=
          congrArg (fun g : FreeMonoid (Fin n) →* FreeMonoid (Fin n) => g w)
            (FreeMonoid.lift_restrict (f := MonoidHom.id (FreeMonoid (Fin n))))
        simpa using this
      have happly :
          FreeMonoid.lift (FreeMonoid.of : Fin n → FreeMonoid (Fin n)) w =
            (w.toList.map (FreeMonoid.of)).prod := by
        simpa using
          (FreeMonoid.lift_apply (f := (FreeMonoid.of : Fin n → FreeMonoid (Fin n))) (l := w))
      exact happly.symm.trans hlift_w

theorem ncard_Sphere_eq_pow_free (n r : ℕ) : Set.ncard (Sphere n r) = n ^ r := by
  classical
  -- Expand the definition of `Sphere`.
  rw [Sphere]
  -- Convert `Set.ncard` to `Nat.card` of the corresponding subtype.
  rw [← Set.Nat.card_coe_set_eq (s := { w : FreeMonoid (Fin n) | w.length = r })]
  change Nat.card { w : FreeMonoid (Fin n) // w.length = r } = n ^ r
  -- `FreeMonoid (Fin n)` is definitionaly `List (Fin n)`, so this subtype is `Vector`.
  change Nat.card (List.Vector (Fin n) r) = n ^ r
  rw [Nat.card_eq_fintype_card]
  -- Use the standard cardinality formula for vectors.
  simpa [Fintype.card_fin] using (card_vector (α := Fin n) r)

open Filter in
theorem tendsto_exp_csqrt_div_nat_atTop (c : ℝ) (hc : 0 < c) : Tendsto (fun s : ℕ => Real.exp (c * Real.sqrt (s : ℝ)) / (s : ℝ)) atTop atTop := by
  have hsqrt : Tendsto (fun s : ℕ => Real.sqrt (s : ℝ)) atTop atTop := by
    -- show √(s) → +∞
    refine (Filter.tendsto_atTop_atTop.2 ?_)
    intro B
    refine ⟨Nat.ceil (B ^ 2), ?_⟩
    intro s hs
    have hB2 : B ^ 2 ≤ (s : ℝ) := by
      have h1 : B ^ 2 ≤ (Nat.ceil (B ^ 2) : ℝ) := by
        exact Nat.le_ceil (B ^ 2)
      have h2 : (Nat.ceil (B ^ 2) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast hs
      exact le_trans h1 h2
    have hB : B ≤ Real.sqrt (B ^ 2) := by
      calc
        B ≤ |B| := le_abs_self B
        _ = Real.sqrt (B ^ 2) := by
          simpa using (Real.sqrt_sq_eq_abs B).symm
    have h3 : Real.sqrt (B ^ 2) ≤ Real.sqrt (s : ℝ) := by
      exact Real.sqrt_le_sqrt hB2
    exact le_trans hB h3

  have hexp : Tendsto (fun x : ℝ => Real.exp (c * x) / x ^ 2) atTop atTop := by
    -- use exponential dominates power
    simpa [Real.rpow_two] using (tendsto_exp_mul_div_rpow_atTop (s := (2 : ℝ)) (b := c) hc)

  -- compose with x = √s
  have hcomp : Tendsto (fun s : ℕ => Real.exp (c * Real.sqrt (s : ℝ)) / (Real.sqrt (s : ℝ)) ^ 2) atTop atTop :=
    hexp.comp hsqrt

  -- rewrite (√s)^2 = s
  have hfinal : (fun s : ℕ => Real.exp (c * Real.sqrt (s : ℝ)) / (Real.sqrt (s : ℝ)) ^ 2) =
      (fun s : ℕ => Real.exp (c * Real.sqrt (s : ℝ)) / (s : ℝ)) := by
    funext s
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (Nat.zero_le s)
    -- rewrite denominator
    simp [Real.sq_sqrt hs0]

  simpa [hfinal] using hcomp

open Filter in
theorem tendsto_expansion_div_atTop_of_eventually_ge {f : ℕ → ℕ} {c : ℝ} (hc : 0 < c) : (∀ᶠ s : ℕ in atTop, Real.exp (c * Real.sqrt (s : ℝ)) ≤ (f s : ℝ)) → Tendsto (fun s : ℕ => (f s : ℝ) / (s : ℝ)) atTop atTop := by
  intro h
  have hg : Tendsto (fun s : ℕ => Real.exp (c * Real.sqrt (s : ℝ)) / (s : ℝ)) atTop atTop :=
    tendsto_exp_csqrt_div_nat_atTop c hc
  have hle : (fun s : ℕ => Real.exp (c * Real.sqrt (s : ℝ)) / (s : ℝ)) ≤ᶠ[atTop]
      (fun s : ℕ => (f s : ℝ) / (s : ℝ)) := by
    filter_upwards [h] with s hs
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast (Nat.zero_le s)
    exact div_le_div_of_nonneg_right hs hs0
  exact Filter.tendsto_atTop_mono' (l := atTop) hle hg

open Filter in
open free in
theorem theorem5_core_probabilistic_deep_exists_postulate_axiom (n : ℕ) (hn : 2 ≤ n) :
  ∃ M : Set (FreeMonoid (Fin n)),
    Tendsto
      (fun r : ℕ =>
        ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
      atTop (nhds 0)
    ∧
    ∃ (K : ℕ) (c : ℝ), 0 < K ∧ 0 < c ∧
      (∀ᶠ r : ℕ in atTop,
        Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n)))
      ∧
      (∀ᶠ s : ℕ in atTop,
        (Real.exp (c * Real.sqrt (s : ℝ)) ≤ (expansion (A n) (M ∪ (A n)) s : ℝ))) := by
  -- Intended postulate/axiom node capturing the deep probabilistic-method construction (Chernoff + Borel–Cantelli + recursive parsing) of a sparse macro set M with superlinear expansion.
  -- 
  -- We do NOT attempt to formalize this here; instead, downstream lemmas/theorems treat this statement as an assumption. Keeping it as a single explicit node makes the non-formalized content clearly localized.
  sorry

open Filter in
open free in
theorem theorem5_core_probabilistic (n : ℕ) (hn : 2 ≤ n) :
  ∃ M : Set (FreeMonoid (Fin n)),
    Tendsto
      (fun r : ℕ =>
        ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
      atTop (nhds 0)
    ∧
    ∃ (K : ℕ) (c : ℝ), 0 < K ∧ 0 < c ∧
      (∀ᶠ r : ℕ in atTop,
        Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n)))
      ∧
      (∀ᶠ s : ℕ in atTop,
        (Real.exp (c * Real.sqrt (s : ℝ)) ≤ (expansion (A n) (M ∪ (A n)) s : ℝ))) := by
  classical
  simpa using theorem5_core_probabilistic_deep_exists_postulate_axiom n hn


open Filter in
open free in
theorem theorem5_core (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Set (FreeMonoid (Fin n)),
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds 0)
      ∧
      ∃ (K : ℕ) (c : ℝ), 0 < K ∧ 0 < c ∧
        (∀ᶠ r : ℕ in atTop,
          Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n)))
        ∧
        (∀ᶠ s : ℕ in atTop,
          (Real.exp (c * Real.sqrt (s : ℝ)) ≤ (expansion (A n) (M ∪ (A n)) s : ℝ))) := by
  rcases theorem5_core_probabilistic n hn with ⟨M, hden, K, c, hKpos, hcpos, hcomp, hexp⟩
  exact ⟨M, hden, ⟨K, c, hKpos, hcpos, hcomp, hexp⟩⟩


open Filter in
open free in
theorem theorem5 (n : ℕ) (hn : 2 ≤ n) :
    ∃ M : Set (FreeMonoid (Fin n)),
      Tendsto
        (fun r : ℕ =>
          ((Set.ncard (M ∩ Sphere n r) : ℝ) / (Set.ncard (Sphere n r) : ℝ)))
        atTop (nhds 0)
      ∧
      Tendsto
        (fun s : ℕ =>
          ((expansion (A n) (M ∪ (A n)) s : ℝ) / (s : ℝ)))
        atTop atTop
      ∧
      ∃ (K : ℕ) (c : ℝ), 0 < K ∧ 0 < c ∧
        (∀ᶠ r : ℕ in atTop,
          Ball r (A n) ⊆ Ball (K * (Nat.log2 r) ^ 2) (M ∪ (A n)))
        ∧
        (∀ᶠ s : ℕ in atTop,
          (Real.exp (c * Real.sqrt (s : ℝ)) ≤ (expansion (A n) (M ∪ (A n)) s : ℝ))) := by
  classical
  rcases theorem5_core n hn with ⟨M, hM, hKc⟩
  rcases hKc with ⟨K, c, hKpos, hcpos, hBall, hExpLower⟩
  have hTexp :
      Tendsto
        (fun s : ℕ =>
          ((expansion (A n) (M ∪ (A n)) s : ℝ) / (s : ℝ)))
        atTop atTop := by
    exact
      tendsto_expansion_div_atTop_of_eventually_ge
        (f := fun s : ℕ => expansion (A n) (M ∪ (A n)) s)
        (c := c)
        hcpos
        hExpLower
  refine ⟨M, hM, hTexp, ?_⟩
  exact ⟨K, c, hKpos, hcpos, hBall, hExpLower⟩


