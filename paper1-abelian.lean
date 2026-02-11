import Mathlib

open scoped BigOperators

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

theorem A_finite (n : ℕ) : (A n).Finite := by
  classical
  simpa [A] using (Set.finite_range fun i : Fin n => ({i} : FreeAbelianMonoid n))

theorem Ball_empty {n R : ℕ} :
    Ball (n:=n) R (∅ : Set (FreeAbelianMonoid n)) = ({0} : Set (FreeAbelianMonoid n)) := by
  ext m
  constructor
  · intro hm
    rcases (by simpa [Ball] using hm) with ⟨l, hlR, hmem, hsum⟩
    cases l with
    | nil =>
        have hm0 : m = 0 := by
          simpa using hsum.symm
        simpa [Set.mem_singleton_iff] using hm0
    | cons a t =>
        have hfalse : False := by
          have : a ∈ (∅ : Set (FreeAbelianMonoid n)) := hmem a (by simp)
          simpa using this
        exact False.elim hfalse
  · intro hm
    have hm0 : m = 0 := by
      simpa [Set.mem_singleton_iff] using hm
    subst hm0
    simp [Ball]
    refine ⟨([] : List (FreeAbelianMonoid n)), ?_, ?_, ?_⟩
    · simp
    · simp
    · simp

theorem Ball_mono_radius {n : ℕ} {R R' : ℕ} {X : Set (FreeAbelianMonoid n)} (h : R ≤ R') :
    Ball (n:=n) R X ⊆ Ball (n:=n) R' X := by
  intro m hm
  rcases hm with ⟨l, hl, hX, hlSum⟩
  refine ⟨l, ?_, hX, hlSum⟩
  exact le_trans hl h

theorem singleton_mem_Ball_A {n : ℕ} (i : Fin n) {R : ℕ} (hR : 1 ≤ R) :
    ({i} : FreeAbelianMonoid n) ∈ Ball (n:=n) R (A n) := by
  classical
  refine ⟨[{i}], ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa using hR
  · intro x hx
    rcases (by simpa using hx) with rfl
    exact ⟨i, rfl⟩
  · simp

theorem theorem_2_quasi_exponential_expansion (n : ℕ) :
    ∃ (G : Set (FreeAbelianMonoid n)) (c q : ℝ) (K : ℕ),
      (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤
            c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) ∧
        (∀ (s : ℕ), (s ≥ 2) →
          let r := Int.toNat <| Int.floor <| Real.exp (K * s * (Real.log s))
          Ball r (A n) ⊆ Ball s G) := by
  classical
  refine ⟨A n, ((A n).ncard : ℝ), (0 : ℝ), (0 : ℕ), ?_, ?_⟩
  · intro r
    simp [Real.rpow_zero]
    have hsubset : (A n ∩ Ball r (A n)) ⊆ A n := by
      intro x hx
      exact hx.1
    exact Set.ncard_le_ncard hsubset (A_finite n)
  · intro s hs
    have hs1 : (1 : ℕ) ≤ s := by
      exact le_trans (by decide : (1 : ℕ) ≤ 2) hs
    dsimp
    have hr : Int.toNat (Int.floor (Real.exp ((0 : ℕ) * s * (Real.log s)))) = 1 := by
      simp
    simpa [hr] using (Ball_mono_radius (n:=n) (R:=1) (R':=s) (X:=A n) hs1)
