/-
  OEIS A189286 (`conjecture_3`): Complete Lean 4 Proof
  ====================================================
  Formalizes and proves the full conjecture for all n ≥ 1:
    Let t(k) = C(6k, 3k) * C(3k, k), S(n) = ∑_{k=0}^n t(k) * t(n - k),
    denom(n) = (2n - 1) * C(3n, n), and a(n) = S(n) / denom(n) (with denom(n) ∣ S(n)).
    Then for all n ≥ 1:
      8 ∣ a(n)  ∧  ((a(n) / 8) % 2 = 1 ↔ ∃ r : Nat, n = 2 ^ r).

  Pure Lean 4 (v4.14.0 core, no Mathlib), zero `sorry`, standard axioms only.
-/

namespace ConjectureLab.OeisA189286

/-! ## 1. Binary digit sum `s2` and 2-adic valuation `v2` -/

/-- Sum of binary digits (popcount) of `n`. -/
def s2 (n : Nat) : Nat :=
  if n = 0 then 0 else n % 2 + s2 (n / 2)
termination_by n
decreasing_by omega

theorem s2_zero : s2 0 = 0 := by simp [s2]

theorem s2_eq (n : Nat) (hn : 0 < n) : s2 n = n % 2 + s2 (n / 2) := by
  rw [s2]
  have hne : n ≠ 0 := by omega
  simp [hne]

theorem s2_two_mul (n : Nat) : s2 (2 * n) = s2 n := by
  cases n with
  | zero => simp [s2_zero]
  | succ m =>
    rw [s2_eq (2 * (m + 1)) (by omega)]
    have h1 : (2 * (m + 1)) % 2 = 0 := by omega
    have h2 : (2 * (m + 1)) / 2 = m + 1 := by omega
    rw [h1, h2, Nat.zero_add]

theorem s2_two_mul_add_one (n : Nat) : s2 (2 * n + 1) = s2 n + 1 := by
  rw [s2_eq (2 * n + 1) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2, Nat.add_comm]

theorem s2_pos (n : Nat) (hn : 0 < n) : 1 ≤ s2 n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hmod : n % 2 = 0
    · have hdiv : 0 < n / 2 := by omega
      have hlt : n / 2 < n := by omega
      have := ih (n / 2) hlt hdiv
      rw [s2_eq n hn, hmod, Nat.zero_add]
      exact this
    · rw [s2_eq n hn]
      omega

/-- No positive multiple of `3` can equal a power of `2` (so `s2 (3 * n) ≥ 2` for `n ≥ 1`). -/
theorem three_mul_ne_pow2 : ∀ (r n : Nat), 0 < n → 3 * n ≠ 2 ^ r
  | 0, n, hn => by simp only [Nat.pow_zero]; omega
  | r + 1, n, hn => by
    intro heq
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at heq
    have heven : n % 2 = 0 := by omega
    have hdiv : 3 * (n / 2) = 2 ^ r := by omega
    exact three_mul_ne_pow2 r (n / 2) (by omega) hdiv

theorem s2_eq_one_iff_pow2 (n : Nat) (hn : 0 < n) : s2 n = 1 ↔ ∃ r : Nat, n = 2 ^ r := by
  constructor
  · intro hs
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn1 : n = 1
      · exact ⟨0, by simp [hn1]⟩
      · by_cases hmod : n % 2 = 0
        · have hdiv : 0 < n / 2 := by omega
          have hlt : n / 2 < n := by omega
          have hs' : s2 (n / 2) = 1 := by
            rw [s2_eq n hn, hmod, Nat.zero_add] at hs
            exact hs
          obtain ⟨r, hr⟩ := ih (n / 2) hlt hdiv hs'
          refine ⟨r + 1, ?_⟩
          rw [Nat.pow_succ, ← hr]
          omega
        · exfalso
          have hdiv : 0 < n / 2 := by omega
          have := s2_pos (n / 2) hdiv
          rw [s2_eq n hn] at hs
          omega
  · rintro ⟨r, rfl⟩
    induction r with
    | zero =>
      rw [Nat.pow_zero, s2_eq 1 (by omega)]
      simp [s2_zero]
    | succ r ih =>
      rw [Nat.pow_succ, Nat.mul_comm, s2_two_mul]
      exact ih (Nat.pow_pos (by omega))

theorem s2_three_mul_pow2 (r : Nat) : s2 (3 * 2 ^ r) = 2 := by
  induction r with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one]
    have h3 : (3 : Nat) = 2 * 1 + 1 := by omega
    rw [h3, s2_two_mul_add_one]
    have h1 : (1 : Nat) = 2 * 0 + 1 := by omega
    rw [h1, s2_two_mul_add_one, s2_zero]
  | succ r ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ r) 2, ← Nat.mul_assoc, Nat.mul_comm 3 2, Nat.mul_assoc,
        s2_two_mul]
    exact ih

/-- 2-adic valuation `v2 n` (returns `0` for `n = 0`). -/
def v2 (n : Nat) : Nat :=
  if n = 0 then 0
  else if n % 2 = 0 then 1 + v2 (n / 2)
  else 0
termination_by n
decreasing_by omega

theorem v2_zero : v2 0 = 0 := by simp [v2]

theorem v2_two_mul (n : Nat) (hn : 0 < n) : v2 (2 * n) = 1 + v2 n := by
  rw [v2]
  have h1 : 2 * n ≠ 0 := by omega
  have h2 : (2 * n) % 2 = 0 := by omega
  have h3 : (2 * n) / 2 = n := by omega
  simp [h1, h2, h3]

theorem v2_two_mul_add_one (n : Nat) : v2 (2 * n + 1) = 0 := by
  rw [v2]
  have h1 : 2 * n + 1 ≠ 0 := by omega
  have h2 : (2 * n + 1) % 2 ≠ 0 := by omega
  simp [h1, h2]

theorem v2_even (n : Nat) (hn : 0 < n) (he : n % 2 = 0) : v2 n = 1 + v2 (n / 2) := by
  have hdiv : 0 < n / 2 := by omega
  have hne : n = 2 * (n / 2) := by omega
  calc v2 n = v2 (2 * (n / 2)) := by rw [← hne]
    _ = 1 + v2 (n / 2) := v2_two_mul (n / 2) hdiv

theorem v2_odd (n : Nat) (ho : n % 2 ≠ 0) : v2 n = 0 := by
  have hno : n = 2 * (n / 2) + 1 := by omega
  calc v2 n = v2 (2 * (n / 2) + 1) := by rw [← hno]
    _ = 0 := v2_two_mul_add_one (n / 2)

theorem pow2_v2_dvd (n : Nat) : 2 ^ v2 n ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; exact ⟨0, by simp⟩
    · by_cases hmod : n % 2 = 0
      · have hdiv : 0 < n / 2 := by omega
        have hlt : n / 2 < n := by omega
        obtain ⟨q, hq⟩ := ih (n / 2) hlt
        rw [v2_even n (by omega) hmod, Nat.add_comm, Nat.pow_succ]
        refine ⟨q, ?_⟩
        calc n = 2 * (n / 2) := by omega
          _ = 2 * (2 ^ v2 (n / 2) * q) := congrArg (2 * ·) hq
          _ = (2 ^ v2 (n / 2) * 2) * q := by
            rw [Nat.mul_comm 2 (2 ^ v2 (n / 2) * q), Nat.mul_assoc, Nat.mul_comm q 2,
                ← Nat.mul_assoc]
      · rw [v2_odd n hmod, Nat.pow_zero]
        exact Nat.one_dvd n

theorem pow2_succ_v2_not_dvd (n : Nat) (hn : 0 < n) : ¬ (2 ^ (v2 n + 1) ∣ n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hmod : n % 2 = 0
    · have hdiv : 0 < n / 2 := by omega
      have hlt : n / 2 < n := by omega
      rw [v2_even n hn hmod]
      intro ⟨q, hq⟩
      apply ih (n / 2) hlt hdiv
      refine ⟨q, ?_⟩
      have hpow : 2 ^ (1 + v2 (n / 2) + 1) = 2 * 2 ^ (v2 (n / 2) + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (v2 (n / 2) + 1), Nat.pow_succ, Nat.mul_comm]
      rw [hpow, Nat.mul_assoc] at hq
      omega
    · rw [v2_odd n hmod, Nat.zero_add, Nat.pow_one]
      intro ⟨q, hq⟩
      omega

theorem pow2_dvd_mono {a b n : Nat} (hle : a ≤ b) (hd : 2 ^ b ∣ n) : 2 ^ a ∣ n := by
  have hsub : b = a + (b - a) := by omega
  rw [hsub, Nat.pow_add] at hd
  exact Nat.dvd_trans (Nat.dvd_mul_right (2 ^ a) (2 ^ (b - a))) hd

theorem pow2_dvd_iff_le_v2 (k n : Nat) (hn : 0 < n) : 2 ^ k ∣ n ↔ k ≤ v2 n := by
  constructor
  · intro hd
    by_cases hle : k ≤ v2 n
    · exact hle
    · exfalso
      have hge : v2 n + 1 ≤ k := by omega
      exact pow2_succ_v2_not_dvd n hn (pow2_dvd_mono hge hd)
  · intro hle
    exact pow2_dvd_mono hle (pow2_v2_dvd n)

theorem v2_mul (a b : Nat) (ha : 0 < a) (hb : 0 < b) : v2 (a * b) = v2 a + v2 b := by
  obtain ⟨oa, hoa⟩ := pow2_v2_dvd a
  obtain ⟨ob, hob⟩ := pow2_v2_dvd b
  have hoa_odd : oa % 2 = 1 := by
    by_cases hodd : oa % 2 = 1
    · exact hodd
    · exfalso
      have hq : oa = 2 * (oa / 2) := by omega
      apply pow2_succ_v2_not_dvd a ha
      refine ⟨oa / 2, ?_⟩
      rw [Nat.pow_succ]
      calc a = 2 ^ v2 a * oa := hoa
        _ = 2 ^ v2 a * (2 * (oa / 2)) := congrArg (2 ^ v2 a * ·) hq
        _ = (2 ^ v2 a * 2) * (oa / 2) := by rw [← Nat.mul_assoc]
  have hob_odd : ob % 2 = 1 := by
    by_cases hodd : ob % 2 = 1
    · exact hodd
    · exfalso
      have hq : ob = 2 * (ob / 2) := by omega
      apply pow2_succ_v2_not_dvd b hb
      refine ⟨ob / 2, ?_⟩
      rw [Nat.pow_succ]
      calc b = 2 ^ v2 b * ob := hob
        _ = 2 ^ v2 b * (2 * (ob / 2)) := congrArg (2 ^ v2 b * ·) hq
        _ = (2 ^ v2 b * 2) * (ob / 2) := by rw [← Nat.mul_assoc]
  have hmul : a * b = 2 ^ (v2 a + v2 b) * (oa * ob) := by
    rw [hoa, hob, Nat.pow_add]
    calc (2 ^ v2 a * oa) * (2 ^ v2 b * ob)
        = 2 ^ v2 a * (oa * (2 ^ v2 b * ob)) := by rw [Nat.mul_assoc]
      _ = 2 ^ v2 a * ((oa * 2 ^ v2 b) * ob) := by rw [Nat.mul_assoc oa]
      _ = 2 ^ v2 a * ((2 ^ v2 b * oa) * ob) := by rw [Nat.mul_comm oa (2 ^ v2 b)]
      _ = (2 ^ v2 a * 2 ^ v2 b) * (oa * ob) := by rw [Nat.mul_assoc (2 ^ v2 b), ← Nat.mul_assoc]
  have hdvd : 2 ^ (v2 a + v2 b) ∣ a * b := ⟨oa * ob, hmul⟩
  have hnot : ¬ (2 ^ (v2 a + v2 b + 1) ∣ a * b) := by
    intro ⟨q, hq⟩
    rw [hmul, Nat.pow_succ, Nat.mul_assoc] at hq
    have hpos : 0 < 2 ^ (v2 a + v2 b) := Nat.pow_pos (by omega)
    have hcancel : oa * ob = 2 * q := Nat.eq_of_mul_eq_mul_left hpos hq
    have hmod : (oa * ob) % 2 = 1 := by
      rw [Nat.mul_mod, hoa_odd, hob_odd]
    omega
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have h1 : v2 a + v2 b ≤ v2 (a * b) := (pow2_dvd_iff_le_v2 _ _ hab).mp hdvd
  have h2 : ¬ (v2 a + v2 b + 1 ≤ v2 (a * b)) := fun h => hnot ((pow2_dvd_iff_le_v2 _ _ hab).mpr h)
  omega

/-! ## 2. Legendre's formula & Kummer's theorem for `p = 2` -/

theorem v2_succ_add_s2_succ (n : Nat) : v2 (n + 1) + s2 (n + 1) = s2 n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hmod : n % 2 = 0
    · have hn : n = 2 * (n / 2) := by omega
      rw [hn, v2_two_mul_add_one, s2_two_mul_add_one, s2_two_mul]
      omega
    · have hn : n = 2 * (n / 2) + 1 := by omega
      have hlt : n / 2 < n := by omega
      have heq : n + 1 = 2 * (n / 2 + 1) := by omega
      rw [heq, v2_two_mul (n / 2 + 1) (by omega), s2_two_mul]
      have ih' := ih (n / 2) hlt
      rw [hn, s2_two_mul_add_one, Nat.add_assoc 1, ih']
      omega

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem v2_fact_add_s2 (n : Nat) : v2 (fact n) + s2 n = n := by
  induction n with
  | zero => simp [fact, s2_zero, v2_two_mul_add_one 0]
  | succ n ih =>
    rw [fact, v2_mul (n + 1) (fact n) (by omega) (fact_pos n)]
    have h := v2_succ_add_s2_succ n
    omega

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_eq_zero_of_lt : ∀ (n k : Nat), n < k → choose n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose, choose_eq_zero_of_lt n k (by omega), choose_eq_zero_of_lt n (k + 1) (by omega)]

theorem choose_pos : ∀ (n k : Nat), k ≤ n → 0 < choose n k
  | _, 0, _ => by simp [choose]
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
    rw [choose]
    have := choose_pos n k (by omega)
    omega

theorem choose_mul_fact : ∀ (n k : Nat), k ≤ n →
    choose n k * (fact k * fact (n - k)) = fact n
  | n, 0, _ => by simp [choose, fact]
  | 0, k + 1, h => by omega
  | n + 1, k + 1, h => by
    by_cases hkn : k + 1 = n + 1
    · have hkeq : k = n := by omega
      subst hkeq
      rw [choose, choose_eq_zero_of_lt k (k + 1) (by omega), Nat.add_zero]
      have hsub : k + 1 - (k + 1) = 0 := by omega
      rw [hsub]
      have ih := choose_mul_fact k k (Nat.le_refl k)
      have hsub0 : k - k = 0 := by omega
      have h0 : fact 0 = 1 := rfl
      rw [hsub0, h0, Nat.mul_one] at ih
      rw [h0, Nat.mul_one, fact]
      calc choose k k * ((k + 1) * fact k)
          = (choose k k * fact k) * (k + 1) := by
            rw [Nat.mul_comm (k + 1) (fact k), Nat.mul_assoc]
        _ = fact k * (k + 1) := by rw [ih]
        _ = (k + 1) * fact k := Nat.mul_comm _ _
    · have hklt : k + 1 ≤ n := by omega
      have hsub1 : n + 1 - (k + 1) = n - k := by omega
      have hsub2 : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub1, choose, Nat.add_mul]
      have ih1 := choose_mul_fact n k (by omega)
      have ih2 := choose_mul_fact n (k + 1) hklt
      have t1 : choose n k * (fact (k + 1) * fact (n - k)) = (k + 1) * fact n := by
        rw [fact]
        calc choose n k * (((k + 1) * fact k) * fact (n - k))
            = choose n k * ((k + 1) * (fact k * fact (n - k))) := by rw [Nat.mul_assoc (k + 1)]
          _ = (choose n k * (k + 1)) * (fact k * fact (n - k)) := by rw [Nat.mul_assoc]
          _ = ((k + 1) * choose n k) * (fact k * fact (n - k)) := by rw [Nat.mul_comm (choose n k)]
          _ = (k + 1) * (choose n k * (fact k * fact (n - k))) := by rw [Nat.mul_assoc]
          _ = (k + 1) * fact n := by rw [ih1]
      have t2 : choose n (k + 1) * (fact (k + 1) * fact (n - k)) = (n - k) * fact n := by
        have hfac : fact (n - k) = (n - k) * fact (n - (k + 1)) := by
          rw [hsub2, fact, ← hsub2]
        rw [hfac]
        calc choose n (k + 1) * (fact (k + 1) * ((n - k) * fact (n - (k + 1))))
            = choose n (k + 1) * ((n - k) * (fact (k + 1) * fact (n - (k + 1)))) := by
              rw [Nat.mul_left_comm (fact (k + 1)) (n - k)]
          _ = (choose n (k + 1) * (n - k)) * (fact (k + 1) * fact (n - (k + 1))) := by
              rw [Nat.mul_assoc]
          _ = ((n - k) * choose n (k + 1)) * (fact (k + 1) * fact (n - (k + 1))) := by
              rw [Nat.mul_comm (choose n (k + 1))]
          _ = (n - k) * (choose n (k + 1) * (fact (k + 1) * fact (n - (k + 1)))) := by
              rw [Nat.mul_assoc]
          _ = (n - k) * fact n := by rw [ih2]
      rw [t1, t2, ← Nat.add_mul]
      have hsum : (k + 1) + (n - k) = n + 1 := by omega
      rw [hsum, fact]

/-- Kummer's theorem for `p = 2`: `v2 (choose (a + b) a) + s2 (a + b) = s2 a + s2 b`. -/
theorem kummer_v2 (a b : Nat) :
    v2 (choose (a + b) a) + s2 (a + b) = s2 a + s2 b := by
  have hmul := choose_mul_fact (a + b) a (by omega)
  have hsub : a + b - a = b := by omega
  rw [hsub] at hmul
  have hpos1 : 0 < choose (a + b) a := choose_pos (a + b) a (by omega)
  have hpos2 : 0 < fact a * fact b := Nat.mul_pos (fact_pos a) (fact_pos b)
  have hv := congrArg v2 hmul
  rw [v2_mul _ _ hpos1 hpos2, v2_mul _ _ (fact_pos a) (fact_pos b)] at hv
  have hf1 := v2_fact_add_s2 a
  have hf2 := v2_fact_add_s2 b
  have hf3 := v2_fact_add_s2 (a + b)
  omega

theorem s2_add_le (a b : Nat) : s2 (a + b) ≤ s2 a + s2 b := by
  have := kummer_v2 a b
  omega

/-! ## 3. Exact 2-adic valuation of `t k` and sum helpers -/

def t (k : Nat) : Nat :=
  choose (6 * k) (3 * k) * choose (3 * k) k

theorem t_zero : t 0 = 1 := rfl

theorem t_pos (k : Nat) : 0 < t k :=
  Nat.mul_pos (choose_pos (6 * k) (3 * k) (by omega)) (choose_pos (3 * k) k (by omega))

theorem v2_t (k : Nat) : v2 (t k) = 2 * s2 k := by
  have hc1 := kummer_v2 (3 * k) (3 * k)
  have heq6 : 3 * k + 3 * k = 6 * k := by omega
  rw [heq6] at hc1
  have hs6 : s2 (6 * k) = s2 (3 * k) := by
    have : 6 * k = 2 * (3 * k) := by omega
    rw [this, s2_two_mul]
  have hc2 := kummer_v2 k (2 * k)
  have heq3 : k + 2 * k = 3 * k := by omega
  rw [heq3, s2_two_mul] at hc2
  have hv : v2 (t k) = v2 (choose (6 * k) (3 * k)) + v2 (choose (3 * k) k) :=
    v2_mul _ _ (choose_pos _ _ (by omega)) (choose_pos _ _ (by omega))
  omega

theorem v2_t_pair (n k : Nat) (hk : k ≤ n) :
    v2 (t k * t (n - k)) = 2 * (s2 k + s2 (n - k)) := by
  rw [v2_mul _ _ (t_pos k) (t_pos (n - k)), v2_t k, v2_t (n - k)]
  omega

/-- Sum `∑_{k=0}^{m-1} f k`. -/
def sumRange : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | m + 1, f => sumRange m f + f m

theorem sumRange_succ (m : Nat) (f : Nat → Nat) :
    sumRange (m + 1) f = sumRange m f + f m := rfl

theorem dvd_sumRange (d m : Nat) (f : Nat → Nat)
    (h : ∀ k, k < m → d ∣ f k) : d ∣ sumRange m f := by
  induction m with
  | zero => exact Nat.dvd_zero d
  | succ m ih =>
    rw [sumRange_succ]
    exact Nat.dvd_add (ih fun k hk => h k (by omega)) (h m (by omega))

theorem sumRange_congr_mod (d m : Nat) (f g : Nat → Nat)
    (h : ∀ k, k < m → f k % d = g k % d) :
    sumRange m f % d = sumRange m g % d := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ]
    have ih' := ih fun k hk => h k (by omega)
    have hm := h m (by omega)
    rw [Nat.add_mod, ih', hm, ← Nat.add_mod]

theorem sumRange_congr (m : Nat) (f g : Nat → Nat)
    (h : ∀ k, k < m → f k = g k) : sumRange m f = sumRange m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sumRange_succ, sumRange_succ, ih (fun k hk => h k (by omega)), h m (by omega)]

theorem sumRange_add (a b : Nat) (f : Nat → Nat) :
    sumRange (a + b) f = sumRange a f + sumRange b (fun k => f (a + k)) := by
  induction b with
  | zero => simp [sumRange]
  | succ b ih =>
    rw [← Nat.add_assoc a b 1, sumRange_succ, sumRange_succ, ih]
    omega

theorem sumRange_shift (a : Nat) (f : Nat → Nat) :
    sumRange (a + 1) f = f 0 + sumRange a (fun k => f (k + 1)) := by
  have h := sumRange_add 1 a f
  rw [Nat.add_comm 1 a] at h
  rw [h]
  have h1 : sumRange 1 f = f 0 := by simp [sumRange]
  rw [h1]
  congr 1
  apply sumRange_congr
  intro k _
  rw [Nat.add_comm 1 k]

theorem sumRange_rev (a : Nat) (f : Nat → Nat) :
    sumRange a (fun k => f (a - 1 - k)) = sumRange a f := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [sumRange_shift, sumRange_succ]
    have h0 : a + 1 - 1 - 0 = a := by omega
    rw [h0]
    have hrest : sumRange a (fun k => f (a + 1 - 1 - (k + 1))) =
        sumRange a (fun k => f (a - 1 - k)) :=
      sumRange_congr a _ _ (fun k hk => by congr 1; omega)
    rw [hrest, ih, Nat.add_comm]

theorem sumRange_split_pairs (m : Nat) (f : Nat → Nat)
    (hsym : ∀ k, k ≤ m → f k = f (m - k)) :
    (m % 2 = 1 → sumRange (m + 1) f = 2 * sumRange (m / 2 + 1) f) ∧
    (m % 2 = 0 → 0 < m → sumRange (m + 1) f = 2 * sumRange (m / 2) f + f (m / 2)) := by
  refine ⟨?_, ?_⟩
  · intro hodd
    have hm : m + 1 = (m / 2 + 1) + (m / 2 + 1) := by omega
    rw [hm, sumRange_add]
    have h1 : sumRange (m / 2 + 1) (fun k => f (m / 2 + 1 + k)) =
        sumRange (m / 2 + 1) (fun k => f (m / 2 + 1 - 1 - k)) := by
      apply sumRange_congr
      intro k hk
      have hle : m / 2 + 1 - 1 - k ≤ m := by omega
      rw [hsym _ hle]
      congr 1
      omega
    rw [h1, sumRange_rev]
    omega
  · intro heven hpos
    have hm : m + 1 = (m / 2 + 1) + (m / 2) := by omega
    rw [hm, sumRange_add, sumRange_succ]
    have h1 : sumRange (m / 2) (fun k => f (m / 2 + 1 + k)) =
        sumRange (m / 2) (fun k => f (m / 2 - 1 - k)) := by
      apply sumRange_congr
      intro k hk
      have hle : m / 2 - 1 - k ≤ m := by omega
      rw [hsym _ hle]
      congr 1
      omega
    rw [h1, sumRange_rev]
    omega

theorem sumRange_even_odd (m : Nat) (g : Nat → Nat) :
    sumRange (2 * m) g = sumRange m (fun j => g (2 * j)) + sumRange m (fun j => g (2 * j + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h2, sumRange_succ, sumRange_succ, ih, sumRange_succ, sumRange_succ]
    omega

/-! ## 4. Counting odd binomial coefficients `s2 k + s2 (n - k) = s2 n` -/

def isSub (n k : Nat) : Nat :=
  if s2 k + s2 (n - k) = s2 n then 1 else 0

theorem count_isSub (n : Nat) : sumRange (n + 1) (isSub n) = 2 ^ s2 n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      simp [sumRange, isSub, s2_zero]
    · by_cases heven : n % 2 = 0
      · have hm : 0 < n / 2 := by omega
        have hlt : n / 2 < n := by omega
        have hn : n = 2 * (n / 2) := by omega
        rw [hn, sumRange_succ, sumRange_even_odd]
        have hev : sumRange (n / 2) (fun j => isSub (2 * (n / 2)) (2 * j)) =
            sumRange (n / 2) (isSub (n / 2)) := by
          apply sumRange_congr
          intro j hj
          simp only [isSub]
          have hsub : 2 * (n / 2) - 2 * j = 2 * (n / 2 - j) := by omega
          rw [s2_two_mul, hsub, s2_two_mul, s2_two_mul]
        have hzero : sumRange (n / 2) (fun _ => 0) = 0 := by
          induction (n / 2) with
          | zero => rfl
          | succ k ihk => rw [sumRange_succ, ihk]
        have hodd : sumRange (n / 2) (fun j => isSub (2 * (n / 2)) (2 * j + 1)) = 0 := by
          rw [← hzero]
          apply sumRange_congr
          intro j hj
          simp only [isSub]
          have hsub : 2 * (n / 2) - (2 * j + 1) = 2 * (n / 2 - j - 1) + 1 := by omega
          rw [s2_two_mul_add_one, hsub, s2_two_mul_add_one, s2_two_mul]
          have hle1 : s2 (n / 2 - 1) ≤ s2 j + s2 (n / 2 - j - 1) := by
            have hsum : j + (n / 2 - j - 1) = n / 2 - 1 := by omega
            rw [← hsum]
            exact s2_add_le j (n / 2 - j - 1)
          have hsucc := v2_succ_add_s2_succ (n / 2 - 1)
          have hsub1 : n / 2 - 1 + 1 = n / 2 := by omega
          rw [hsub1] at hsucc
          have hneq : s2 j + 1 + (s2 (n / 2 - j - 1) + 1) ≠ s2 (n / 2) := by omega
          simp [hneq]
        have hlast : isSub (2 * (n / 2)) (2 * (n / 2)) = isSub (n / 2) (n / 2) := by
          simp only [isSub]
          have h1 : 2 * (n / 2) - 2 * (n / 2) = 0 := by omega
          have h2 : n / 2 - n / 2 = 0 := by omega
          rw [h1, h2, s2_two_mul, s2_zero]
        rw [hev, hodd, Nat.add_zero, hlast, ← sumRange_succ, ih (n / 2) hlt, s2_two_mul]
      · have hn : n = 2 * (n / 2) + 1 := by omega
        have hlt : n / 2 < n := by omega
        have hn1 : n + 1 = 2 * (n / 2 + 1) := by omega
        rw [hn1, sumRange_even_odd]
        have hs2n : s2 n = s2 (n / 2) + 1 := by
          calc s2 n = s2 (2 * (n / 2) + 1) := by rw [← hn]
            _ = s2 (n / 2) + 1 := s2_two_mul_add_one (n / 2)
        have hev : sumRange (n / 2 + 1) (fun j => isSub n (2 * j)) =
            sumRange (n / 2 + 1) (isSub (n / 2)) := by
          apply sumRange_congr
          intro j hj
          simp only [isSub]
          have hsub : n - 2 * j = 2 * (n / 2 - j) + 1 := by omega
          rw [s2_two_mul, hsub, s2_two_mul_add_one, hs2n]
          have heq : (s2 j + (s2 (n / 2 - j) + 1) = s2 (n / 2) + 1) ↔
              (s2 j + s2 (n / 2 - j) = s2 (n / 2)) := by omega
          simp [heq]
        have hodd : sumRange (n / 2 + 1) (fun j => isSub n (2 * j + 1)) =
            sumRange (n / 2 + 1) (isSub (n / 2)) := by
          apply sumRange_congr
          intro j hj
          simp only [isSub]
          have hsub : n - (2 * j + 1) = 2 * (n / 2 - j) := by omega
          rw [s2_two_mul_add_one, hsub, s2_two_mul, hs2n]
          have heq : (s2 j + 1 + s2 (n / 2 - j) = s2 (n / 2) + 1) ↔
              (s2 j + s2 (n / 2 - j) = s2 (n / 2)) := by omega
          simp [heq]
        rw [hev, hodd, ih (n / 2) hlt, hs2n, Nat.pow_succ]
        have hdouble : 2 ^ s2 (n / 2) + 2 ^ s2 (n / 2) = 2 ^ s2 (n / 2) * 2 := by omega
        exact hdouble

/-! ## 5. Main Theorem (`OeisA189286.conjecture_3`) -/

def S (n : Nat) : Nat :=
  sumRange (n + 1) (fun k => t k * t (n - k))

def denom (n : Nat) : Nat :=
  (2 * n - 1) * choose (3 * n) n

theorem denom_pos (n : Nat) (hn : 1 ≤ n) : 0 < denom n :=
  Nat.mul_pos (by omega) (choose_pos (3 * n) n (by omega))

theorem S_pos (n : Nat) : 0 < S n := by
  rw [S, sumRange_succ]
  have := Nat.mul_pos (t_pos n) (t_pos (n - n))
  omega

theorem v2_S_pow2 (r : Nat) : v2 (S (2 ^ r)) = 3 := by
  let n := 2 ^ r
  have hn : 0 < n := Nat.pow_pos (by omega)
  have hs2n : s2 n = 1 := (s2_eq_one_iff_pow2 n hn).mpr ⟨r, rfl⟩
  have hS_split : S n = t 0 * t n + sumRange (n - 1) (fun k => t (k + 1) * t (n - (k + 1))) + t n * t 0 := by
    rw [S, sumRange_succ]
    have hn_eq : n = 1 + (n - 1) := by omega
    have hsplit1 : sumRange n (fun k => t k * t (n - k)) =
        sumRange 1 (fun k => t k * t (n - k)) +
        sumRange (n - 1) (fun k => t (1 + k) * t (n - (1 + k))) := by
      calc sumRange n (fun k => t k * t (n - k))
          = sumRange (1 + (n - 1)) (fun k => t k * t (n - k)) := by rw [← hn_eq]
        _ = sumRange 1 (fun k => t k * t (n - k)) +
            sumRange (n - 1) (fun k => t (1 + k) * t (n - (1 + k))) := sumRange_add 1 (n - 1) _
    have h0 : sumRange 1 (fun k => t k * t (n - k)) = t 0 * t (n - 0) := by simp [sumRange]
    have hcongr : sumRange (n - 1) (fun k => t (1 + k) * t (n - (1 + k))) =
        sumRange (n - 1) (fun k => t (k + 1) * t (n - (k + 1))) := by
      apply sumRange_congr
      intro k _
      rw [Nat.add_comm 1 k]
    have hsub0 : n - 0 = n := by omega
    have hsubn : n - n = 0 := by omega
    rw [hsplit1, h0, hcongr, hsub0, hsubn]
  have hint : 16 ∣ sumRange (n - 1) (fun k => t (k + 1) * t (n - (k + 1))) := by
    apply dvd_sumRange
    intro k hk
    have hpos1 : 1 ≤ k + 1 := by omega
    have hpos2 : 1 ≤ n - (k + 1) := by omega
    have hs1 : 1 ≤ s2 (k + 1) := s2_pos (k + 1) hpos1
    have hs2 : 1 ≤ s2 (n - (k + 1)) := s2_pos (n - (k + 1)) hpos2
    have hv := v2_t_pair n (k + 1) (by omega)
    have hv4 : 4 ≤ v2 (t (k + 1) * t (n - (k + 1))) := by omega
    exact (pow2_dvd_iff_le_v2 4 _ (Nat.mul_pos (t_pos _) (t_pos _))).mpr hv4
  have hbound : t 0 * t n + t n * t 0 = 2 * t n := by
    rw [t_zero, Nat.one_mul, Nat.mul_one]
    omega
  have hS_eq : S n = 2 * t n + sumRange (n - 1) (fun k => t (k + 1) * t (n - (k + 1))) := by
    rw [hS_split]
    omega
  have hv2t : v2 (2 * t n) = 3 := by
    rw [v2_two_mul (t n) (t_pos n), v2_t n, hs2n]
  have hpos2t : 0 < 2 * t n := Nat.mul_pos (by omega) (t_pos n)
  have hd8 : 8 ∣ 2 * t n := (pow2_dvd_iff_le_v2 3 _ hpos2t).mpr (by omega)
  have hnd16 : ¬ (16 ∣ 2 * t n) := by
    intro h
    have := (pow2_dvd_iff_le_v2 4 _ hpos2t).mp h
    omega
  have hd8_int : 8 ∣ sumRange (n - 1) (fun k => t (k + 1) * t (n - (k + 1))) :=
    Nat.dvd_trans (by decide : 8 ∣ 16) hint
  have hS8 : 8 ∣ S n := by rw [hS_eq]; exact Nat.dvd_add hd8 hd8_int
  have hS16 : ¬ (16 ∣ S n) := by
    intro h
    rw [hS_eq] at h
    have hsub := Nat.dvd_sub (by omega) h hint
    have heq : 2 * t n + sumRange (n - 1) (fun k => t (k + 1) * t (n - (k + 1))) -
        sumRange (n - 1) (fun k => t (k + 1) * t (n - (k + 1))) = 2 * t n := by omega
    rw [heq] at hsub
    exact hnd16 hsub
  have hle : 3 ≤ v2 (S n) := (pow2_dvd_iff_le_v2 3 _ (S_pos n)).mp hS8
  have hlt : ¬ (4 ≤ v2 (S n)) := fun h => hS16 ((pow2_dvd_iff_le_v2 4 _ (S_pos n)).mpr h)
  omega

theorem v2_denom_pow2 (r : Nat) : v2 (denom (2 ^ r)) = 0 := by
  let n := 2 ^ r
  have hn : 0 < n := Nat.pow_pos (by omega)
  have hs2n : s2 n = 1 := (s2_eq_one_iff_pow2 n hn).mpr ⟨r, rfl⟩
  have hv_odd : v2 (2 * n - 1) = 0 := by
    have : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
    rw [this, v2_two_mul_add_one]
  have hkum := kummer_v2 n (2 * n)
  have h3n : n + 2 * n = 3 * n := by omega
  rw [h3n, s2_two_mul] at hkum
  have hs3 : s2 (3 * n) = 2 := s2_three_mul_pow2 r
  rw [denom, v2_mul _ _ (by omega) (choose_pos (3 * n) n (by omega)), hv_odd, Nat.zero_add]
  omega

theorem dvd_S_nonpow2 (n : Nat) (hn : 1 ≤ n) (hnot : ¬ ∃ r : Nat, n = 2 ^ r) :
    2 ^ (2 * s2 n + 2) ∣ S n := by
  have hs_ge2 : 2 ≤ s2 n := by
    have hp := s2_pos n hn
    have hne := mt (s2_eq_one_iff_pow2 n hn).mp hnot
    omega
  let f := fun k => t k * t (n - k)
  have hsym : ∀ k, k ≤ n → f k = f (n - k) := by
    intro k hk
    simp only [f]
    have hsub : n - (n - k) = k := by omega
    rw [hsub, Nat.mul_comm]
  have hsplit := sumRange_split_pairs n f hsym
  let M := 2 * s2 n + 1
  have half_dvd : ∀ m, m ≤ n →
      (sumRange (n + 1) (isSub n) = 2 * sumRange m (isSub n)) →
      2 ^ (M + 1) ∣ 2 * sumRange m f := by
    intro m hm_le hcnt
    have h2 : 2 ^ M ∣ sumRange m f := by
      have hmod : sumRange m f % 2 ^ M = sumRange m (fun k => isSub n k * 2 ^ (2 * s2 n)) % 2 ^ M := by
        apply sumRange_congr_mod
        intro k hk
        have hk_le : k ≤ n := by omega
        simp only [isSub]
        by_cases hsub : s2 k + s2 (n - k) = s2 n
        · simp only [hsub, ↓reduceIte, Nat.one_mul]
          have hfk : f k = t k * t (n - k) := rfl
          have hpos : 0 < f k := Nat.mul_pos (t_pos k) (t_pos (n - k))
          have hv : v2 (f k) = 2 * s2 n := by rw [hfk, v2_t_pair n k hk_le, hsub]
          obtain ⟨o, ho⟩ := pow2_v2_dvd (f k)
          have ho_odd : o % 2 = 1 := by
            by_cases hodd : o % 2 = 1
            · exact hodd
            · exfalso
              have hq : o = 2 * (o / 2) := by omega
              apply pow2_succ_v2_not_dvd (f k) hpos
              refine ⟨o / 2, ?_⟩
              rw [Nat.pow_succ]
              calc f k = 2 ^ v2 (f k) * o := ho
                _ = 2 ^ v2 (f k) * (2 * (o / 2)) := congrArg (2 ^ v2 (f k) * ·) hq
                _ = (2 ^ v2 (f k) * 2) * (o / 2) := by rw [← Nat.mul_assoc]
          rw [hv] at ho
          have ho' : o = 2 * (o / 2) + 1 := by omega
          rw [ho, ho', Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_succ]
          have hM : 2 * s2 n + 1 = M := rfl
          rw [hM, Nat.add_comm, Nat.mul_comm (2 ^ M) (o / 2), Nat.add_mul_mod_self_right]
        · simp only [hsub, ↓reduceIte, Nat.zero_mul]
          have hgt : s2 n < s2 k + s2 (n - k) := by
            have hle := s2_add_le k (n - k)
            have hsum : k + (n - k) = n := by omega
            rw [hsum] at hle
            omega
          have hv : M ≤ v2 (f k) := by
            change M ≤ v2 (t k * t (n - k))
            rw [v2_t_pair n k hk_le]
            omega
          have hd : 2 ^ M ∣ f k := (pow2_dvd_iff_le_v2 M (f k) (Nat.mul_pos (t_pos _) (t_pos _))).mpr hv
          exact Nat.mod_eq_zero_of_dvd hd
      have hfactor : ∀ r, sumRange r (fun k => isSub n k * 2 ^ (2 * s2 n)) =
          sumRange r (isSub n) * 2 ^ (2 * s2 n) := by
        intro r
        induction r with
        | zero => simp [sumRange]
        | succ r ihr => rw [sumRange_succ, sumRange_succ, ihr, Nat.add_mul]
      rw [hfactor m] at hmod
      have hcnt_pow : sumRange m (isSub n) = 2 ^ (s2 n - 1) := by
        rw [count_isSub n] at hcnt
        have hpow : 2 ^ s2 n = 2 * 2 ^ (s2 n - 1) := by
          have : s2 n = (s2 n - 1) + 1 := by omega
          rw [this, Nat.pow_succ, Nat.mul_comm]
        rw [hpow] at hcnt
        omega
      rw [hcnt_pow] at hmod
      have heven_cnt : 2 ∣ 2 ^ (s2 n - 1) := by
        have hsplit_s : s2 n - 1 = (s2 n - 2) + 1 := by omega
        rw [hsplit_s, Nat.pow_succ]
        exact Nat.dvd_mul_left 2 _
      obtain ⟨q, hq⟩ := heven_cnt
      have hdvd_rhs : 2 ^ M ∣ 2 ^ (s2 n - 1) * 2 ^ (2 * s2 n) := by
        rw [hq]
        refine ⟨q, ?_⟩
        have hMpow : 2 ^ M = 2 ^ (2 * s2 n) * 2 := Nat.pow_succ 2 (2 * s2 n)
        rw [hMpow]
        calc (2 * q) * 2 ^ (2 * s2 n)
            = q * (2 * 2 ^ (2 * s2 n)) := by rw [Nat.mul_comm 2 q, Nat.mul_assoc]
          _ = q * (2 ^ (2 * s2 n) * 2) := by rw [Nat.mul_comm 2]
          _ = (2 ^ (2 * s2 n) * 2) * q := by rw [Nat.mul_comm]
      rw [Nat.mod_eq_zero_of_dvd hdvd_rhs] at hmod
      exact Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨q, hq⟩ := h2
    refine ⟨q, ?_⟩
    rw [hq, Nat.pow_succ]
    calc 2 * (2 ^ M * q) = (2 * 2 ^ M) * q := by rw [← Nat.mul_assoc]
      _ = (2 ^ M * 2) * q := by rw [Nat.mul_comm 2]
  by_cases hodd : n % 2 = 1
  · rw [S, hsplit.1 hodd]
    have hcnt : sumRange (n + 1) (isSub n) = 2 * sumRange (n / 2 + 1) (isSub n) := by
      have hsym_sub : ∀ k, k ≤ n → isSub n k = isSub n (n - k) := by
        intro k hk
        simp only [isSub]
        have hsub : n - (n - k) = k := by omega
        rw [hsub, Nat.add_comm (s2 k)]
      exact (sumRange_split_pairs n (isSub n) hsym_sub).1 hodd
    exact half_dvd (n / 2 + 1) (by omega) hcnt
  · have heven : n % 2 = 0 := by omega
    rw [S, hsplit.2 heven hn]
    have hcnt : sumRange (n + 1) (isSub n) = 2 * sumRange (n / 2) (isSub n) := by
      have hsym_sub : ∀ k, k ≤ n → isSub n k = isSub n (n - k) := by
        intro k hk
        simp only [isSub]
        have hsub : n - (n - k) = k := by omega
        rw [hsub, Nat.add_comm (s2 k)]
      have hsp := (sumRange_split_pairs n (isSub n) hsym_sub).2 heven hn
      have hmid : isSub n (n / 2) = 0 := by
        simp only [isSub]
        have hsub : n - n / 2 = n / 2 := by omega
        have hn2 : n = 2 * (n / 2) := by omega
        rw [hsub]
        have hs2eq : s2 n = s2 (n / 2) := by
          calc s2 n = s2 (2 * (n / 2)) := by rw [← hn2]
            _ = s2 (n / 2) := s2_two_mul (n / 2)
        rw [hs2eq]
        have hp : 1 ≤ s2 (n / 2) := s2_pos (n / 2) (by omega)
        have hneq : s2 (n / 2) + s2 (n / 2) ≠ s2 (n / 2) := by omega
        simp [hneq]
      rw [hsp, hmid, Nat.add_zero]
    have h1 := half_dvd (n / 2) (by omega) hcnt
    have hmid_dvd : 2 ^ (M + 1) ∣ f (n / 2) := by
      have hpos : 0 < f (n / 2) := Nat.mul_pos (t_pos _) (t_pos _)
      have hv : M + 1 ≤ v2 (f (n / 2)) := by
        change M + 1 ≤ v2 (t (n / 2) * t (n - n / 2))
        have hsub : n - n / 2 = n / 2 := by omega
        have hn2 : n = 2 * (n / 2) := by omega
        rw [v2_t_pair n (n / 2) (by omega), hsub]
        have hs_eq : s2 (n / 2) = s2 n := by
          calc s2 (n / 2) = s2 (2 * (n / 2)) := (s2_two_mul (n / 2)).symm
            _ = s2 n := by rw [← hn2]
        omega
      exact (pow2_dvd_iff_le_v2 (M + 1) (f (n / 2)) hpos).mpr hv
    exact Nat.dvd_add h1 hmid_dvd

/-- Complete Lean 4 proof of OEIS A189286 (`conjecture_3`):
    assuming integrality `denom n ∣ S n` (known from `conjecture_1`), for all `n ≥ 1`,
    `8 ∣ a(n)` and `(a(n) / 8) % 2 = 1 ↔ ∃ r, n = 2 ^ r`. -/
theorem conjecture_3 (n : Nat) (hn : 1 ≤ n) (hdvd : denom n ∣ S n) :
    8 ∣ (S n / denom n) ∧ ((S n / denom n) / 8 % 2 = 1 ↔ ∃ r : Nat, n = 2 ^ r) := by
  let a_n := S n / denom n
  have ha_mul : a_n * denom n = S n := Nat.div_mul_cancel hdvd
  have ha_pos : 0 < a_n := by
    by_cases h0 : 0 < a_n
    · exact h0
    · exfalso
      have ha0 : a_n = 0 := Nat.eq_zero_of_not_pos h0
      rw [ha0, Nat.zero_mul] at ha_mul
      have := S_pos n
      omega
  have hv_mul : v2 a_n + v2 (denom n) = v2 (S n) := by
    rw [← v2_mul a_n (denom n) ha_pos (denom_pos n hn), ha_mul]
  by_cases hpow2 : ∃ r : Nat, n = 2 ^ r
  · obtain ⟨r, rfl⟩ := hpow2
    have hvS := v2_S_pow2 r
    have hvD := v2_denom_pow2 r
    have hva : v2 a_n = 3 := by omega
    have h8 : 8 ∣ a_n := (pow2_dvd_iff_le_v2 3 a_n ha_pos).mpr (by omega)
    have h16 : ¬ (16 ∣ a_n) := fun h => by
      have := (pow2_dvd_iff_le_v2 4 a_n ha_pos).mp h
      omega
    have hmod : a_n / 8 % 2 = 1 := by
      obtain ⟨q, hq⟩ := h8
      have hq_div : a_n / 8 = q := by rw [hq, Nat.mul_comm 8 q, Nat.mul_div_cancel q (by omega)]
      rw [hq_div]
      by_cases hq1 : q % 2 = 1
      · exact hq1
      · exfalso
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero (by omega : q % 2 = 0)
        apply h16
        refine ⟨k, ?_⟩
        rw [hq, hk]
        omega
    exact ⟨h8, ⟨fun _ => ⟨r, rfl⟩, fun _ => hmod⟩⟩
  · have hS_dvd := dvd_S_nonpow2 n hn hpow2
    have hleS : 2 * s2 n + 2 ≤ v2 (S n) := (pow2_dvd_iff_le_v2 _ _ (S_pos n)).mp hS_dvd
    have hkum := kummer_v2 n (2 * n)
    have h3n : n + 2 * n = 3 * n := by omega
    rw [h3n, s2_two_mul] at hkum
    have hv_odd : v2 (2 * n - 1) = 0 := by
      have : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
      rw [this, v2_two_mul_add_one]
    have hvD : v2 (denom n) = v2 (choose (3 * n) n) := by
      rw [denom, v2_mul _ _ (by omega) (choose_pos (3 * n) n (by omega)), hv_odd, Nat.zero_add]
    have hs3 : 2 ≤ s2 (3 * n) := by
      have hpos3 := s2_pos (3 * n) (by omega)
      have hne1 : s2 (3 * n) ≠ 1 := by
        intro h1
        obtain ⟨r, hr⟩ := (s2_eq_one_iff_pow2 (3 * n) (by omega)).mp h1
        exact three_mul_ne_pow2 r n hn hr
      omega
    have hva : 4 ≤ v2 a_n := by omega
    have h16 : 16 ∣ a_n := (pow2_dvd_iff_le_v2 4 a_n ha_pos).mpr hva
    have h8 : 8 ∣ a_n := Nat.dvd_trans (by decide : 8 ∣ 16) h16
    have hmod : a_n / 8 % 2 = 0 := by
      obtain ⟨q, hq⟩ := h16
      have h8q : a_n = 8 * (2 * q) := by omega
      have hdiv : a_n / 8 = 2 * q := by
        rw [h8q, Nat.mul_comm 8 (2 * q), Nat.mul_div_cancel (2 * q) (by omega)]
      rw [hdiv]
      omega
    refine ⟨h8, ⟨fun h1 => by omega, fun h => absurd h hpow2⟩⟩

end ConjectureLab.OeisA189286
