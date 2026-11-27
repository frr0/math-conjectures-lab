import Mathlib.Tactic

/-
  OEIS A001481 (J. Lowell, Jan 14 2022)
  =====================================
  "Barring the 0+2, 0+4, 0+8, 0+16, ... sequence, the sum of 2 distinct terms
   in this sequence is never a power of 2."

  Full formalization: if `a ≠ b` are both sums of two squares and `a + b = 2^k`,
  then `{a, b} = {0, 2^k}`. Conversely every `2^k` is a sum of two squares.
  Proof: 2-adic descent using that odd sums of two squares are `1 mod 4`.
-/

namespace ConjectureLab.OeisA001481

/-- `n` is a term of A001481: a sum of two squares of natural numbers. -/
def IsSumTwoSq (n : ℕ) : Prop := ∃ x y : ℕ, n = x ^ 2 + y ^ 2

theorem sq_mod_four (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with h | h | h | h <;>
    simp [h]

theorem sq_mod_two (x : ℕ) : x ^ 2 % 2 = x % 2 := by
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

/-- Odd sums of two squares are `1 mod 4`. -/
theorem mod_four_of_odd {n : ℕ} (hn : IsSumTwoSq n) (hodd : n % 2 = 1) : n % 4 = 1 := by
  obtain ⟨x, y, rfl⟩ := hn
  have hx := sq_mod_four x
  have hy := sq_mod_four y
  generalize x ^ 2 = X at *
  generalize y ^ 2 = Y at *
  omega

/-- If `2m` is a sum of two squares, so is `m`. -/
theorem half {m : ℕ} (h : IsSumTwoSq (2 * m)) : IsSumTwoSq m := by
  obtain ⟨x, y, hxy⟩ := h
  have hpar : x % 2 = y % 2 := by
    have h1 := sq_mod_two x
    have h2 := sq_mod_two y
    generalize x ^ 2 = X at *
    generalize y ^ 2 = Y at *
    omega
  rcases le_total y x with hle | hle
  · obtain ⟨t, rfl⟩ : ∃ t, x = y + 2 * t := ⟨(x - y) / 2, by omega⟩
    refine ⟨y + t, t, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_⟩
    rw [hxy]; ring
  · obtain ⟨t, rfl⟩ : ∃ t, y = x + 2 * t := ⟨(y - x) / 2, by omega⟩
    refine ⟨x + t, t, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_⟩
    rw [hxy]; ring

/-- Core descent: two distinct sums of two squares adding to `2^k` include `0`. -/
theorem zero_of_sum_pow_two (k : ℕ) :
    ∀ a b : ℕ, IsSumTwoSq a → IsSumTwoSq b → a ≠ b → a + b = 2 ^ k → a = 0 ∨ b = 0 := by
  induction k with
  | zero =>
    intro a b _ _ _ h
    rw [pow_zero] at h
    omega
  | succ k ih =>
    intro a b ha hb hne h
    rw [pow_succ] at h
    rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · obtain ⟨a', rfl⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
      obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
      have hP : a' + b' = 2 ^ k := by
        generalize 2 ^ k = P at h
        omega
      rcases ih a' b' (half ha) (half hb) (by omega) hP with h0 | h0 <;> omega
    · generalize 2 ^ k = P at h
      omega
    · generalize 2 ^ k = P at h
      omega
    · have ha4 := mod_four_of_odd ha ha2
      have hb4 := mod_four_of_odd hb hb2
      rcases k with _ | k
      · rw [pow_zero] at h
        omega
      · rw [pow_succ] at h
        generalize 2 ^ k = P at h
        omega

/-- Every power of two is a sum of two squares (the exceptional family is genuine). -/
theorem pow_two_isSumTwoSq (k : ℕ) : IsSumTwoSq (2 ^ k) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · exact ⟨2 ^ j, 0, by ring⟩
  · exact ⟨2 ^ j, 2 ^ j, by ring⟩

/-- **Lowell's conjecture (OEIS A001481), proved.** Distinct sums of two squares
`a, b` with `a + b = 2^k` are exactly `{0, 2^k}`. -/
theorem lowell_conjecture (a b k : ℕ) (ha : IsSumTwoSq a) (hb : IsSumTwoSq b)
    (hne : a ≠ b) (h : a + b = 2 ^ k) :
    (a = 0 ∧ b = 2 ^ k) ∨ (a = 2 ^ k ∧ b = 0) := by
  have h0 := zero_of_sum_pow_two k a b ha hb hne h
  generalize 2 ^ k = P at *
  omega

end ConjectureLab.OeisA001481
