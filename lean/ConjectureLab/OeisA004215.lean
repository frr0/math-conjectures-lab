import Mathlib.Tactic

/-
  OEIS A004215 (Tilman Neumann, Sep 20 2020)
  ==========================================
  "The number of terms < 2^n is A023105(n) - 2."

  By Legendre's three-square theorem, A004215 = {4^a (8b+7)}. This module proves
  that for every m ≥ 1,
      #{n < 2^m : n = 4^a (8b+7)} + 2 = ⌊(2^m + 10) / 6⌋,
  and the right-hand side is the classical closed form of A023105(m).
  The proof uses the recurrence C(m+3) = 2^m + C(m+1).
  Scope (🟢): this module does not formalize Legendre's theorem or the residue
  count for A023105. Both are proved or cited in results/oeis-a004215/README.md.
-/

namespace ConjectureLab.OeisA004215

/-- Legendre's form `4^a (8b+7)`: the terms of A004215. -/
def IsLegendreForm (n : ℕ) : Prop := ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)

theorem seven_le {n : ℕ} (h : IsLegendreForm n) : 7 ≤ n := by
  obtain ⟨a, b, rfl⟩ := h
  have : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
  nlinarith

theorem form_iff (n : ℕ) :
    IsLegendreForm n ↔ n % 8 = 7 ∨ (n % 4 = 0 ∧ IsLegendreForm (n / 4)) := by
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases a with _ | a
    · left
      rw [pow_zero, one_mul]
      omega
    · right
      have e : 4 ^ (a + 1) * (8 * b + 7) = 4 * (4 ^ a * (8 * b + 7)) := by ring
      rw [e]
      exact ⟨Nat.mul_mod_right _ _, a, b, Nat.mul_div_cancel_left _ (by norm_num)⟩
  · rintro (h | ⟨h4, a, b, hab⟩)
    · exact ⟨0, n / 8, by rw [pow_zero, one_mul]; omega⟩
    · refine ⟨a + 1, b, ?_⟩
      have hn : n = 4 * (n / 4) := by omega
      rw [hn, hab]
      ring

open Classical in
/-- Terms of Legendre's form below `2^m`. -/
noncomputable def S (m : ℕ) : Finset ℕ := (Finset.range (2 ^ m)).filter IsLegendreForm

theorem S_step (m : ℕ) :
    S (m + 3) = (Finset.range (2 ^ m)).image (fun b => 8 * b + 7) ∪
      (S (m + 1)).image (fun n => 4 * n) := by
  ext n
  simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  rw [form_iff n]
  have h3 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
  have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  rw [h3, h1]
  generalize 2 ^ m = P
  constructor
  · rintro ⟨hlt, h | ⟨h4, hf⟩⟩
    · exact Or.inl ⟨n / 8, by omega, by omega⟩
    · exact Or.inr ⟨n / 4, ⟨by omega, hf⟩, by omega⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨k, ⟨hk, hf⟩, rfl⟩)
    · exact ⟨by omega, Or.inl (by omega)⟩
    · refine ⟨by omega, Or.inr ⟨by omega, ?_⟩⟩
      rwa [Nat.mul_div_cancel_left k (by norm_num : 0 < 4)]

theorem card_step (m : ℕ) : (S (m + 3)).card = 2 ^ m + (S (m + 1)).card := by
  have i1 : Function.Injective (fun b : ℕ => 8 * b + 7) := fun x y h => by
    have h' : 8 * x + 7 = 8 * y + 7 := h
    omega
  have i2 : Function.Injective (fun n : ℕ => 4 * n) := fun x y h => by
    have h' : 4 * x = 4 * y := h
    omega
  have hd : Disjoint ((Finset.range (2 ^ m)).image (fun b => 8 * b + 7))
      ((S (m + 1)).image (fun n => 4 * n)) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_image] at hn hn'
    obtain ⟨b, _, rfl⟩ := hn
    obtain ⟨k, _, hk⟩ := hn'
    omega
  rw [S_step, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ i1,
    Finset.card_image_of_injective _ i2, Finset.card_range]

open Classical in
theorem card_small (m : ℕ) (hm : m ≤ 2) : (S m).card = 0 := by
  rw [Finset.card_eq_zero, S, Finset.filter_eq_empty_iff]
  intro x hx hP
  have h7 := seven_le hP
  have h4 : 2 ^ m ≤ 4 := by interval_cases m <;> norm_num
  rw [Finset.mem_range] at hx
  omega

theorem card_odd (j : ℕ) : 6 * (S (2 * j + 1)).card + 2 = 2 ^ (2 * j + 1) := by
  induction j with
  | zero => rw [card_small _ (by norm_num)]; norm_num
  | succ j ih =>
    have hs := card_step (2 * j)
    rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring] at hs
    have p1 : 2 ^ (2 * (j + 1) + 1) = 8 * 2 ^ (2 * j) := by ring
    have p2 : 2 ^ (2 * j + 1) = 2 * 2 ^ (2 * j) := by ring
    rw [p1, hs]
    rw [p2] at ih
    omega

theorem card_even (j : ℕ) : 6 * (S (2 * j + 2)).card + 4 = 2 ^ (2 * j + 2) := by
  induction j with
  | zero => rw [card_small _ (by norm_num)]; norm_num
  | succ j ih =>
    have hs := card_step (2 * j + 1)
    rw [show 2 * j + 1 + 3 = 2 * (j + 1) + 2 by ring,
      show 2 * j + 1 + 1 = 2 * j + 2 by ring] at hs
    have p1 : 2 ^ (2 * (j + 1) + 2) = 8 * 2 ^ (2 * j + 1) := by ring
    have p2 : 2 ^ (2 * j + 2) = 2 * 2 ^ (2 * j + 1) := by ring
    rw [p1, hs]
    rw [p2] at ih
    omega

/-- **Neumann's conjecture (OEIS A004215), counting core.** For `m ≥ 1`,
`#{n < 2^m : n = 4^a(8b+7)} = ⌊(2^m + 10)/6⌋ - 2 = A023105(m) - 2`. -/
theorem neumann_count (m : ℕ) (hm : 1 ≤ m) : (S m).card + 2 = (2 ^ m + 10) / 6 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h := card_even i
    rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    omega
  · have h := card_odd j
    omega

end ConjectureLab.OeisA004215
