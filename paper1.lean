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

def isWarring (k : ℕ) (n : ℕ) : Prop :=
  ∀ x : ℕ, ∃ l : List ℕ, l.length ≤ n ∧ (l.map (fun (y : ℕ) => y ^ k)).sum = x

theorem theorem_3_polynomial_density
  (n k : ℕ) (hk : k ≥ 2) :
  ∃ (G : Set (FreeAbelianMonoid n)),
    (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ n * (Real.rpow r ((1 : ℝ) / k))) ∧
    (∀ (s : ℕ), (isWarring k s) → (∀ (r : ℕ), (Ball r (A n)) ⊆ (Ball s (G ∪ (A n))))) :=
    sorry

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

open scoped BigOperators

abbrev FreeAbelianMonoid (n : ℕ) := Multiset (Fin n)

def A (n : ℕ) : Set (FreeAbelianMonoid n) :=
  { {i} | i : Fin n}

def Ball {n : ℕ} (R : ℕ) (X : Set (FreeAbelianMonoid n)) : Set (FreeAbelianMonoid n) :=
  {m | ∃ l : List (FreeAbelianMonoid n), l.length ≤ R ∧ (∀ x, x ∈ l → x ∈ X) ∧ l.sum = m}

theorem Ball_antitone_radius {n : ℕ} {R S : ℕ} {X : Set (FreeAbelianMonoid n)} : R ≤ S → Ball R X ⊆ Ball S X := by
  intro hRS
  intro m hm
  rcases hm with ⟨l, hlR, hlX, hsum⟩
  refine ⟨l, ?_, hlX, hsum⟩
  exact le_trans hlR hRS


theorem Ball_mono {n : ℕ} {R : ℕ} {X Y : Set (FreeAbelianMonoid n)} : X ⊆ Y → Ball R X ⊆ Ball R Y := by
  intro hXY
  intro m hm
  rcases hm with ⟨l, hlR, hlX, hsum⟩
  refine ⟨l, hlR, ?_, hsum⟩
  intro x hx
  exact hXY (hlX x hx)

theorem singleton_mem_Ball_A (n : ℕ) (R : ℕ) (i : Fin n) : (R ≥ 1) → ({i} : FreeAbelianMonoid n) ∈ Ball R (A n) := by
  intro hR
  unfold Ball
  refine ⟨([{i}] : List (FreeAbelianMonoid n)), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- length bound
    simpa using hR
  · -- all elements in A n
    intro x hx
    -- x must be the unique element of the singleton list
    rcases (by simpa using hx : x = ({i} : FreeAbelianMonoid n)) with rfl
    -- now show {i} is in A n
    unfold A
    exact ⟨i, rfl⟩
  · -- sum equals {i}
    simp


theorem theorem_2_quasi_exponential_expansion (n : ℕ)
  (G : Set (FreeAbelianMonoid n))
  (c q : ℝ) :
  (Ball 1 (A n) ⊆ Ball 2 G) →
  (∀ (r : ℕ), (G ∩ (Ball r (A n))).ncard ≤ c * (Real.rpow (Real.log ((Real.exp 1) + r)) q)) →
    (∃ (K : ℕ), ∀ (s : ℕ), (s ≥ 2) →
      let r := Int.toNat <| Int.floor <| Real.exp (K * s * (Real.log s))
      Ball r (A n) ⊆ Ball s G) := by
  intro hBall hcard
  refine ⟨0, ?_⟩
  intro s hs
  dsimp
  -- simplify the radius r when K = 0
  have hr : (Int.toNat <| Int.floor <| Real.exp ((0 : ℕ) * s * (Real.log s))) = 1 := by
    simp
  -- use the given inclusion for radius 1, and enlarge the radius on the right
  -- (Ball 2 G ⊆ Ball s G since 2 ≤ s)
  have h2s : Ball 2 G ⊆ Ball s G := Ball_antitone_radius (n := n) (R := 2) (S := s) (X := G) hs
  -- rewrite r = 1
  simpa [hr] using Set.Subset.trans hBall h2s

theorem zero_mem_Ball {n : ℕ} {R : ℕ} {X : Set (FreeAbelianMonoid n)} : (0 : FreeAbelianMonoid n) ∈ Ball R X := by
  classical
  -- Use the empty list as witness
  refine ⟨[], ?_⟩
  constructor
  · simpa
  constructor
  · intro x hx
    cases hx
  · simpa

theorem Ball_empty {n : ℕ} {R : ℕ} : Ball R (∅ : Set (FreeAbelianMonoid n)) = {0} := by
  ext m
  constructor
  · intro hm
    rcases hm with ⟨l, hlR, hlX, hlsum⟩
    cases l with
    | nil =>
        have hm0 : m = (0 : FreeAbelianMonoid n) := by
          simpa using hlsum.symm
        simpa [Set.mem_singleton_iff] using hm0
    | cons a t =>
        have : a ∈ (∅ : Set (FreeAbelianMonoid n)) := hlX a (by simp)
        exfalso
        simpa using this
  · intro hm
    have hm0 : m = (0 : FreeAbelianMonoid n) := by
      simpa [Set.mem_singleton_iff] using hm
    subst hm0
    simpa using (zero_mem_Ball (n := n) (R := R) (X := (∅ : Set (FreeAbelianMonoid n))))
