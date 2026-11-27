import Mathlib.Tactic

/-
  OEIS A001227 (Omar E. Pol, Feb 15 2017)
  =======================================
  "Conjectures: a(n) = A067742(n) + 2*A131576(n) = A082647(n) + A131576(n)."

  All four sequences are defined below directly from their OEIS names:
    * A001227(n): number of odd divisors of n;
    * A067742(n): number of divisors d of n with sqrt(n/2) <= d < sqrt(2n);
    * A131576(n): ways to write n as a sum of an even number of consecutive positive integers;
    * A082647(n): ways to write n as a sum of d consecutive positive integers with d | n.
  With A = {odd d | n : d² < 2n} and B = {odd d | n : d² > 2n} we show
    A082647 = |A|,  A131576 = |B|,  A001227 = |A| + |B|,  A067742 + |B| = |A|,
  which gives both identities (`pol_conjecture`). Full formalization (✅).
-/

namespace ConjectureLab.OeisA001227

open Finset

/-- Representations `n = m + (m+1) + ... + (m+k-1)` with `m, k ≥ 1`, as pairs `(m, k)`.
The box `[1, n]²` loses nothing, see `mem_runs`. -/
def runs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter fun p => ∑ i ∈ range p.2, (p.1 + i) = n

/-- A001227: number of odd divisors of `n`. -/
def a001227 (n : ℕ) : ℕ := (n.divisors.filter Odd).card

open Classical in
/-- A067742: number of middle divisors of `n`, i.e. divisors in `[sqrt(n/2), sqrt(2n))`. -/
noncomputable def a067742 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ =>
    Real.sqrt ((n : ℝ) / 2) ≤ (d : ℝ) ∧ (d : ℝ) < Real.sqrt (2 * (n : ℝ))).card

/-- A131576: ways to write `n` as a sum of an even number of consecutive positive integers. -/
def a131576 (n : ℕ) : ℕ := ((runs n).filter fun p => Even p.2).card

/-- A082647: ways to write `n` as a sum of `d` consecutive positive integers, `d ∣ n`. -/
def a082647 (n : ℕ) : ℕ := ((runs n).filter fun p => p.2 ∣ n).card

/-! ### Arithmetic of runs -/

theorem run_sum (m k : ℕ) : 2 * (∑ i ∈ range k, (m + i)) + k = k * (2 * m + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; nlinarith

/-- `runs n` is exactly the set of all representations (no hidden bound). -/
theorem mem_runs {n : ℕ} {p : ℕ × ℕ} :
    p ∈ runs n ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ ∑ i ∈ range p.2, (p.1 + i) = n := by
  obtain ⟨m, k⟩ := p
  simp only [runs, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, h2, -⟩, h⟩
    exact ⟨h1, h2, h⟩
  · rintro ⟨h1, h2, h⟩
    have e := run_sum m k
    rw [h] at e
    refine ⟨⟨⟨h1, by nlinarith⟩, h2, by nlinarith⟩, h⟩

theorem mem_runs' {n : ℕ} {p : ℕ × ℕ} :
    p ∈ runs n ↔ 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ 2 * n + p.2 = p.2 * (2 * p.1 + p.2) := by
  rw [mem_runs]
  have e := run_sum p.1 p.2
  constructor
  · rintro ⟨h1, h2, h⟩
    exact ⟨h1, h2, by rw [← h]; exact e⟩
  · rintro ⟨h1, h2, h⟩
    exact ⟨h1, h2, by omega⟩

/-! ### Odd divisors split at `d² = 2n` -/

/-- Odd divisors below `√(2n)`. -/
def A (n : ℕ) : Finset ℕ := n.divisors.filter fun d => Odd d ∧ d * d < 2 * n

/-- Odd divisors above `√(2n)`. -/
def B (n : ℕ) : Finset ℕ := n.divisors.filter fun d => Odd d ∧ 2 * n < d * d

theorem odd_sq_ne {d n : ℕ} (hd : Odd d) : d * d ≠ 2 * n := by
  have h := Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨hd, hd⟩)
  generalize d * d = s at h
  omega

theorem a001227_eq (n : ℕ) : a001227 n = (A n).card + (B n).card := by
  have h1 : (n.divisors.filter Odd).filter (fun d => d * d < 2 * n) = A n := by
    ext d; simp only [A, mem_filter]; tauto
  have h2 : (n.divisors.filter Odd).filter (fun d => ¬ d * d < 2 * n) = B n := by
    ext d
    simp only [B, mem_filter]
    constructor
    · rintro ⟨⟨h, ho⟩, hlt⟩
      exact ⟨h, ho, lt_of_le_of_ne (not_lt.mp hlt) (odd_sq_ne ho).symm⟩
    · rintro ⟨h, ho, hlt⟩
      exact ⟨⟨h, ho⟩, by omega⟩
  rw [a001227, ← filter_card_add_filter_neg_card_eq_card (fun d => d * d < 2 * n), h1, h2]

/-- In a run, `k ∣ n` iff `k` is odd. -/
theorem dvd_iff_odd {n m k : ℕ} (hk : 1 ≤ k) (h : 2 * n + k = k * (2 * m + k)) : k ∣ n ↔ Odd k := by
  constructor
  · rintro ⟨q, rfl⟩
    rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ho
    · exfalso
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · omega
      · have h' : (r + r) * (2 * q + 1) = (r + r) * (2 * m + (r + r)) := by rw [← h]; ring
        have := Nat.eq_of_mul_eq_mul_left (by omega) h'
        omega
    · exact ho
  · intro ho
    have h2 : k ∣ 2 * n := ⟨2 * m + k - 1, by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at ho
      · have : 2 * m + k = (2 * m + k - 1) + 1 := by omega
        rw [this, mul_add, mul_one] at h
        omega⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.coprime_comm.mp ((Nat.coprime_two_left).mpr ho)) h2)

theorem a082647_eq (n : ℕ) : a082647 n = (A n).card := by
  rw [a082647]
  apply card_bij (fun p _ => p.2)
  · intro p hp
    rw [mem_filter, mem_runs'] at hp
    obtain ⟨⟨h1, h2, h⟩, hd⟩ := hp
    have ho := (dvd_iff_odd h2 h).mp hd
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, ?_⟩, ho, ?_⟩
    · rintro rfl; nlinarith
    · nlinarith
  · intro p hp q hq hpq
    rw [mem_filter, mem_runs'] at hp hq
    obtain ⟨⟨-, h2, h⟩, -⟩ := hp
    obtain ⟨⟨-, -, h'⟩, -⟩ := hq
    simp only at hpq
    rw [← hpq] at h'
    have : p.2 * (2 * p.1 + p.2) = p.2 * (2 * q.1 + p.2) := by omega
    have := Nat.eq_of_mul_eq_mul_left (by omega) this
    exact Prod.ext (by omega) hpq
  · intro d hd
    simp only [A, mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨q, rfl⟩, hn⟩, ho, hlt⟩ := hd
    -- d * d < 2 d q, so d < 2q; start m = (2q + 1 - d) / 2
    have hdq : d < 2 * q := by nlinarith
    obtain ⟨r, rfl⟩ := ho
    refine ⟨(q - r, 2 * r + 1), ?_, rfl⟩
    rw [mem_filter, mem_runs']
    refine ⟨⟨by omega, by omega, ?_⟩, Dvd.intro q rfl⟩
    simp only
    have : 2 * (q - r) + (2 * r + 1) = 2 * q + 1 := by omega
    rw [this]; ring

theorem a131576_eq (n : ℕ) : a131576 n = (B n).card := by
  rw [a131576]
  apply card_bij (fun p _ => 2 * p.1 + p.2 - 1)
  · intro p hp
    rw [mem_filter, mem_runs'] at hp
    obtain ⟨⟨h1, h2, h⟩, r, hr⟩ := hp
    rw [hr] at h
    have hj : 2 * p.1 + (r + r) - 1 + 1 = 2 * p.1 + (r + r) := by omega
    generalize hJ : 2 * p.1 + (r + r) - 1 = j at hj
    rw [hr, hJ]
    rw [← hj] at h
    have hn : n = r * j := by nlinarith
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨⟨r, by rw [hn, mul_comm]⟩, ?_⟩, ⟨p.1 + r - 1, by omega⟩, ?_⟩
    · rintro rfl
      have : r * j = 0 := hn.symm
      rcases Nat.mul_eq_zero.mp this with h0 | h0 <;> omega
    · rw [hn]
      have : r + r < j := by omega
      nlinarith
  · intro p hp q hq hpq
    rw [mem_filter, mem_runs'] at hp hq
    obtain ⟨⟨h1, h2, h⟩, -⟩ := hp
    obtain ⟨⟨h1', h2', h'⟩, -⟩ := hq
    simp only at hpq
    have e1 : p.2 * (2 * p.1 + p.2 - 1) = 2 * n := by
      have : 2 * p.1 + p.2 = (2 * p.1 + p.2 - 1) + 1 := by omega
      rw [this, mul_add, mul_one] at h; omega
    have e2 : q.2 * (2 * q.1 + q.2 - 1) = 2 * n := by
      have : 2 * q.1 + q.2 = (2 * q.1 + q.2 - 1) + 1 := by omega
      rw [this, mul_add, mul_one] at h'; omega
    rw [hpq] at e1
    rw [← e2] at e1
    have hk := Nat.eq_of_mul_eq_mul_right (by omega) e1
    exact Prod.ext (by omega) hk
  · intro d hd
    simp only [B, mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨q, rfl⟩, hn⟩, ho, hlt⟩ := hd
    -- 2 d q < d * d, so 2q < d; run of length 2q starting at (d + 1 - 2q) / 2
    have hq : 2 * q < d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · simp at ho
      · nlinarith
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · simp at hn
      · exact h
    obtain ⟨r, rfl⟩ := ho
    refine ⟨(r + 1 - q, 2 * q), ?_, ?_⟩
    · rw [mem_filter, mem_runs']
      refine ⟨⟨by omega, by omega, ?_⟩, ⟨q, by ring⟩⟩
      simp only
      have : 2 * (r + 1 - q) + 2 * q = 2 * r + 2 := by omega
      rw [this]; ring
    · simp only; omega

/-! ### Middle divisors -/

theorem middle_iff (n d : ℕ) :
    (Real.sqrt ((n : ℝ) / 2) ≤ (d : ℝ) ∧ (d : ℝ) < Real.sqrt (2 * (n : ℝ))) ↔
      (n ≤ 2 * (d * d) ∧ d * d < 2 * n) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [Real.sqrt_le_iff, Real.lt_sqrt hd]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    constructor
    · have : (n : ℝ) ≤ 2 * ((d : ℝ) * d) := by nlinarith
      exact_mod_cast this
    · have : ((d : ℝ) * d) < 2 * n := by nlinarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (n : ℝ) ≤ 2 * ((d : ℝ) * d) := by exact_mod_cast h1
    have h2' : ((d : ℝ) * d) < 2 * n := by exact_mod_cast h2
    exact ⟨⟨hd, by nlinarith⟩, by nlinarith⟩

/-- Divisors below `√(2n)`. -/
def S (n : ℕ) : Finset ℕ := n.divisors.filter fun d => d * d < 2 * n

/-- Divisors below `√(n/2)`. -/
def U (n : ℕ) : Finset ℕ := n.divisors.filter fun d => 2 * (d * d) < n

theorem a067742_add (n : ℕ) : a067742 n + (U n).card = (S n).card := by
  have hM : a067742 n = ((S n).filter fun d => ¬ 2 * (d * d) < n).card := by
    rw [a067742, S, filter_filter]
    exact congrArg card (by ext d; simp only [mem_filter, middle_iff, not_lt]; tauto)
  have hU : U n = (S n).filter fun d => 2 * (d * d) < n := by
    rw [U, S, filter_filter]
    ext d
    simp only [mem_filter]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, by omega, h'⟩
    · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
  rw [hM, hU, add_comm, filter_card_add_filter_neg_card_eq_card]

/-- Even divisors below `√(n/2)` correspond to the `d ∈ U n` with `2d ∣ n` via doubling. -/
theorem card_U_dvd (n : ℕ) :
    ((U n).filter fun d => 2 * d ∣ n).card = ((S n).filter Even).card := by
  apply card_bij (fun d _ => 2 * d)
  · intro d hd
    simp only [U, S, mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨⟨-, hn⟩, h⟩, h2⟩ := hd
    exact ⟨⟨⟨h2, hn⟩, by nlinarith⟩, ⟨d, by ring⟩⟩
  · intro a _ b _ h; omega
  · intro e he
    simp only [U, S, mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨⟨hdv, hn⟩, h⟩, ⟨r, rfl⟩⟩ := he
    refine ⟨r, ?_, by ring⟩
    simp only [U, mem_filter, Nat.mem_divisors]
    have h2 : 2 * r ∣ n := by rw [two_mul]; exact hdv
    exact ⟨⟨⟨dvd_trans (Dvd.intro_left 2 rfl) h2, hn⟩, by nlinarith⟩, h2⟩

/-- The `d ∈ U n` with `2d ∤ n` correspond to `B n` via `d ↦ n / d`. -/
theorem card_U_ndvd (n : ℕ) :
    ((U n).filter fun d => ¬ 2 * d ∣ n).card = (B n).card := by
  apply card_bij (fun d _ => n / d)
  · intro d hd
    simp only [U, B, mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨⟨⟨⟨q, rfl⟩, hn⟩, h⟩, h2⟩ := hd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h0
      · simp at hn
      · exact h0
    rw [Nat.mul_div_cancel_left q hd0]
    refine ⟨⟨Dvd.intro_left d rfl, hn⟩, ?_, ?_⟩
    · rcases Nat.even_or_odd q with ⟨r, rfl⟩ | ho
      · exact absurd ⟨r, by ring⟩ h2
      · exact ho
    · nlinarith
  · intro a ha b hb h
    simp only [U, mem_filter, Nat.mem_divisors] at ha hb
    obtain ⟨⟨⟨ha', hn⟩, -⟩, -⟩ := ha
    obtain ⟨⟨⟨hb', -⟩, -⟩, -⟩ := hb
    rw [← Nat.div_div_self ha' hn, h, Nat.div_div_self hb' hn]
  · intro e he
    simp only [B, mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨⟨q, rfl⟩, hn⟩, ho, h⟩ := he
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | h0
      · simp at hn
      · exact h0
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with rfl | h0
      · simp at hn
      · exact h0
    have h2q : 2 * q < e := by nlinarith
    refine ⟨q, ?_, by rw [Nat.mul_div_cancel _ hq0]⟩
    simp only [U, mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨Dvd.intro_left e rfl, hn⟩, by nlinarith⟩, ?_⟩
    rintro ⟨c, hc⟩
    have : e = 2 * c := by
      have : q * e = q * (2 * c) := by rw [mul_comm q e, hc]; ring
      exact Nat.eq_of_mul_eq_mul_left hq0 this
    obtain ⟨r, hr⟩ := ho
    omega

theorem a067742_add_B (n : ℕ) : a067742 n + (B n).card = (A n).card := by
  have h1 := a067742_add n
  have h2 := filter_card_add_filter_neg_card_eq_card (s := U n) (fun d => 2 * d ∣ n)
  have hS := filter_card_add_filter_neg_card_eq_card (s := S n) Even
  have hA : (S n).filter (fun d => ¬ Even d) = A n := by
    rw [S, A, filter_filter]
    ext d
    simp only [mem_filter, Nat.not_even_iff_odd]
    tauto
  rw [card_U_dvd, card_U_ndvd] at h2
  rw [hA] at hS
  omega

/-- **Pol's conjecture (OEIS A001227), Feb 15 2017.** For every `n`,
`A001227(n) = A067742(n) + 2·A131576(n) = A082647(n) + A131576(n)`. -/
theorem pol_conjecture (n : ℕ) :
    a001227 n = a067742 n + 2 * a131576 n ∧ a001227 n = a082647 n + a131576 n := by
  have h := a067742_add_B n
  rw [a001227_eq, a131576_eq, a082647_eq]
  omega

end ConjectureLab.OeisA001227
