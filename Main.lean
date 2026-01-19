import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Antiufeev

open scoped BigOperators

abbrev Sn (n : ℕ) := Equiv.Perm (Fin n)

/-- The transposition `(12)` on `Fin n` (0-based: swap `0` and `1`).
For `n < 2` we define it as the identity permutation. -/
def δ : ∀ n : ℕ, Sn n
  | 0 => 1
  | 1 => 1
  | (Nat.succ (Nat.succ _)) => Equiv.swap 0 1

/-- The long cycle `(1 2 ... n)` as a rotation of `Fin n` by one step (0-based: `(0 1 ... n-1)`). -/
def r (n : ℕ) : Sn n := finRotate n

/-- The generating set `{ (12), (1 2 ... n), (1 n ... 2) } = {δ, r, r⁻¹}` as a finset. -/
def gens (n : ℕ) : Finset (Sn n) :=
  let ρ := r n
  { δ n, ρ, ρ⁻¹ }

/-- An undirected Cayley graph (as a `SimpleGraph`) from a finite generating set `S`. -/
def cayleyGraph {G : Type*} [Group G] [DecidableEq G] (S : Finset G) : SimpleGraph G where
  Adj g h := g ≠ h ∧ ∃ s ∈ S, g * s = h ∨ h * s = g
  symm := by
    intro g h
    rintro ⟨hneq, s, hsS, hmul⟩
    refine ⟨by simpa [ne_comm] using hneq, ?_⟩
    refine ⟨s, hsS, ?_⟩
    simpa [or_comm] using hmul
  loopless := by
    intro g
    simp

/-- The Cayley graph `Γₙ` of `Sₙ` with generators `(12)`, `(1 2 … n)`, `(1 n … 2)`. -/
def Γ (n : ℕ) : SimpleGraph (Sn n) :=
  cayleyGraph (gens n)

/-- If `b ≤ a` then `a - (a - b) = b`.  (We prove it by cancelling `a - b` on the right.) -/
private lemma sub_sub_cancel_of_le (a b : ℕ) (h : b ≤ a) :
    a - (a - b) = b := by
  apply Nat.add_right_cancel
  -- goal: a - (a - b) + (a - b) = b + (a - b)
  have hL : a - (a - b) + (a - b) = a :=
    Nat.sub_add_cancel (Nat.sub_le a b)   -- (a - b) ≤ a
  have h1 : (a - b) + b = a :=
    Nat.sub_add_cancel h                  -- b ≤ a
  have hR : b + (a - b) = a :=
    (Nat.add_comm b (a - b)).trans h1
  calc
    a - (a - b) + (a - b) = a := hL
    _ = b + (a - b) := by exact hR.symm

/--
`revPrefixPerm n j` is the permutation of *positions* (indices) that reverses the first `j` entries
in one-line notation (0-based), and fixes positions `j, j+1, ...`.

For the purposes of stating Lemma 1, it is enough to have this object; its internal proofs are omitted.
-/
def revPrefixPerm (n j : ℕ) : Sn n := by
  classical
  -- Let `m = min j n`; we do case split on `m`.
  cases h : Nat.min j n with
  | zero =>
      exact 1
  | succ m' =>
      -- In this branch, `min j n = m'+1`, so in particular `m'+1 ≤ n`.
      have hmle : Nat.succ m' ≤ n := by
        have : Nat.min j n ≤ n := Nat.min_le_right j n
        simpa [h] using this
      -- Define the underlying function `f : Fin n → Fin n`.
      -- If `k < m` we send `k ↦ (m-1-k)`, i.e. `m' - k`, otherwise we fix `k`.
      let f : Fin n → Fin n := fun k =>
        if hk : k.val < Nat.succ m' then
          ⟨m' - k.val, by
            -- show `m' - k.val < n`
            have hle : m' - k.val ≤ m' := Nat.sub_le _ _
            have hlt : m' < Nat.succ m' := Nat.lt_succ_self m'
            have hlt' : m' - k.val < Nat.succ m' := lt_of_le_of_lt hle hlt
            exact lt_of_lt_of_le hlt' hmle⟩
        else
          k

      -- Prove involution: `f (f k) = k` for all `k`.
      have hf : ∀ k : Fin n, f (f k) = k := by
        intro k
        by_cases hk : k.val < Nat.succ m'
        · -- Case: `k` is inside the reversed prefix.
          have hkle : k.val ≤ m' := (Nat.lt_succ_iff).1 hk
          have hk' : (m' - k.val) < Nat.succ m' := by
            have hle : m' - k.val ≤ m' := Nat.sub_le _ _
            exact lt_of_le_of_lt hle (Nat.lt_succ_self m')

          -- arithmetic: if `k ≤ m'` then `m' - (m' - k) = k`
          have hsub : m' - (m' - k.val) = k.val :=
            sub_sub_cancel_of_le m' k.val hkle

          apply Fin.ext
          dsimp [f]
          -- first `if` uses `hk`, second uses `hk'`, and the value uses `hsub`
          simpa [hk, hk', hsub]
        · -- outside the prefix: fixed
          have fk : f k = k := by
            dsimp [f]
            simp [hk]
          calc
            f (f k) = f k := by simp [fk]
            _ = k := fk

      -- Turn the involution into a permutation by setting `invFun = f`.
      exact
        { toFun := f
          invFun := f
          left_inv := hf
          right_inv := hf }

/-- The full reversal `s = [n n-1 ... 1]` as a permutation on `Fin n`. -/
noncomputable def s (n : ℕ) : Sn n :=
  revPrefixPerm n n

theorem Antiufeev_lemma1_1
    (n j : ℕ) (hn : 3 ≤ n) (hj2 : 2 ≤ j) (hj : j ≤ (n + 1) / 2)
    (π : Sn n) :
    let ξ : Sn n := π * revPrefixPerm n j
    (Γ n).dist π (ξ * (r n) ^ ((j / 2) - 1)) = j * (j - 1) - 1 :=
    sorry

/--
**Lemma 1 (Antiufeev).** :contentReference[oaicite:2]{index=2}

Let `π` be a permutation and let `ξ` be obtained from `π` by reversing the first `j` entries in
one-line notation. Assume `n ≥ 3` and `2 ≤ j ≤ ⌈n/2⌉`. Then the four distance equalities (I–IV) hold.
-/
theorem Antiufeev_lemma1
    (n j : ℕ) (hn : 3 ≤ n) (hj2 : 2 ≤ j) (hj : j ≤ (n + 1) / 2)
    (π : Sn n) :
    let ξ : Sn n := π * revPrefixPerm n j
    (Γ n).dist π (ξ * (r n) ^ ((j / 2) - 1)) = j * (j - 1) - 1 ∧
    (Γ n).dist (π * (r n) ^ (j - 2)) (ξ * (r n) ^ (((j + 1) / 2) - 1)) = j * (j - 1) - 1 ∧
    (Γ n).dist (π * (r n) ^ ((j / 2) - 1)) ξ = j * (j - 1) - 1 ∧
    (Γ n).dist (π * (r n) ^ (((j + 1) / 2) - 1)) (ξ * (r n) ^ (j - 2)) = j * (j - 1) - 1 := by
  -- proof in the draft proceeds by counting inversions and optimal swaps
  sorry

/--
Convenience: the RHS in Theorem 1, using `Nat` divisions:
`ceil(n/2) = (n+1)/2` and `floor(n/2) = n/2`. :contentReference[oaicite:3]{index=3}
-/
def theorem1RHS (n i : ℕ) : ℕ :=
  let c : ℕ := (n + 1) / 2     -- ⌈n/2⌉
  let f : ℕ := n / 2           -- ⌊n/2⌋
  (c * (c - 1) - 1) +
  (f * (f - 1) - 1) +
  (if i = 1 then
      f + 1
    else if 2 ≤ i ∧ i ≤ f + 2 then
      f - i + 4
    else
      i - c)
/--
**Theorem 1 (Antiufeev).** :contentReference[oaicite:4]{index=4}

Let `s = [n n-1 ... 1]`, `r = [2 3 ... n 1]` in `Sₙ` with `n ≥ 4`. For `i ∈ {1,2,...,n}`,
the distance from `s * r^(n-i)` to the identity is given by the explicit piecewise formula.
-/

theorem Antiufeev_theorem1
    (n i : ℕ) (hn : 4 ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    (Γ n).dist (s n * (r n) ^ (n - i)) 1 = theorem1RHS n i := by
  -- proof in the draft uses two applications of Lemma 1 and a Lee-metric computation on an orbit
  sorry

/--
**Theorem 2 (Antiufeev).**
A lower bound for the diameter of the Cayley graph of `Sₙ` generated by `(12)`, `(1 2 … n)`, `(1 n … 2)`
is `n(n-1)/2`. :contentReference[oaicite:1]{index=1}
-/
theorem Antiufeev_theorem2 (n : ℕ) (hn : 4 ≤ n) :
    (n * (n - 1)) / 2 ≤ (Γ n).diam := by
  sorry

end Antiufeev
