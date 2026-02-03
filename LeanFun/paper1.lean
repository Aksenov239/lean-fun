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
  (h1 : 1 ≤ n)
  (hb : 2 ≤ b) :
  let M := MacroSet n b
  (∃ (d1 d2 : ℕ), ∀ (x : ℕ), (x ≥ b) → 0 < d1 ∧ 0 < d2
      ∧ d1 * (Real.log x) ≤ (M ∩ (Ball x (A n))).ncard
      ∧ (M ∩ (Ball x (A n))).ncard ≤ d2 * (Real.log x))
    ∧
    ∀ s : ℕ, s ≥ 1 → (
      let r1 := Int.toNat <| Int.ceil <| Real.rpow b ((s : ℝ) / (n * (b - 1)) - 1)
      (Ball r1 (A n) ⊆ (Ball s (M ∪ (A n))))
      ∧
      let r2 := 1 + n * b * (Int.toNat <| Int.floor <| Real.rpow b ((s : ℝ) / (n * (b - 1))))
      ¬ (Ball r2 (A n) ⊆ (Ball s (M ∪ (A n))))) :=
      sorry

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
