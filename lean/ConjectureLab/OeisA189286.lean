/-
  OEIS A189286 (`conjecture_3`): 2-adic Valuation Characterization
  ================================================================
  Formalizes key structural lemmas and exact initial verifications for A189286:
    a(n) = (∑_{k=0}^n t_k t_{n-k}) / ((2n - 1) * C(3n, n)),
    where t_k = C(6k, 3k) * C(3k, k).
  Proves:
    1. For every n ≥ 1, 3n is never a power of 2 (so s_2(3n) ≥ 2).
    2. For s ≥ 2, 2^(s-1) identical terms of valuation 2s + 1 sum to a
       multiple of 2^(2s + 2) (the submask-pairing cancellation lemma).
    3. Exact kernel-verified values a(1) = 40, a(2) = 696, a(3) = 23408,
       a(4) = 969496 and their exact 2-adic behavior mod 16.
-/

namespace ConjectureLab.OeisA189286

/-- Fast multiplicative binomial coefficient `C(n, k)` for kernel evaluation. -/
def binomAux (n k : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | rem + 1, acc =>
    let i := k - (rem + 1)
    binomAux n k rem ((acc * (n - i)) / (i + 1))

def binom (n k : Nat) : Nat :=
  if k > n then 0 else binomAux n k k 1

/-- `t(k) = C(6k, 3k) * C(3k, k)`. -/
def t (k : Nat) : Nat :=
  binom (6 * k) (3 * k) * binom (3 * k) k

/-- Convolution sum `S(n) = ∑_{k=0}^n t(k) * t(n - k)`. -/
def sumLoop (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc + t 0 * t n
  | k + 1, acc => sumLoop n k (acc + t (k + 1) * t (n - (k + 1)))

def S (n : Nat) : Nat :=
  sumLoop n n 0

/-- Exact `a(n)` for `n ≥ 1`. -/
def a (n : Nat) : Nat :=
  S n / ((2 * n - 1) * binom (3 * n) n)

-- Kernel-verified initial values and 2-adic residues mod 16:
theorem a_1_val : a 1 = 40 := rfl
theorem a_2_val : a 2 = 696 := rfl
theorem a_3_val : a 3 = 23408 := rfl
theorem a_4_val : a 4 = 969496 := rfl

theorem a_1_mod16 : a 1 % 8 = 0 ∧ (a 1 / 8) % 2 = 1 := ⟨rfl, rfl⟩
theorem a_2_mod16 : a 2 % 8 = 0 ∧ (a 2 / 8) % 2 = 1 := ⟨rfl, rfl⟩
theorem a_3_mod16 : a 3 % 8 = 0 ∧ (a 3 / 8) % 2 = 0 := ⟨rfl, rfl⟩
theorem a_4_mod16 : a 4 % 8 = 0 ∧ (a 4 / 8) % 2 = 1 := ⟨rfl, rfl⟩

/-- No positive multiple of `3` can equal a power of `2` (so `s_2(3n) ≥ 2` for `n ≥ 1`). -/
theorem three_mul_ne_pow2 : ∀ (r n : Nat), 0 < n → 3 * n ≠ 2 ^ r
  | 0, n, hn => by
    simp only [Nat.pow_zero]
    omega
  | r + 1, n, hn => by
    intro heq
    have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at heq
    have heven : n % 2 = 0 := by omega
    have hdiv : 3 * (n / 2) = 2 ^ r := by omega
    exact three_mul_ne_pow2 r (n / 2) (by omega) hdiv

/-- Submask-pairing cancellation lemma: when `s ≥ 2`, `2^(s-1)` pairs each
    contributing `2^(2s + 1)` sum to a multiple of `2^(2s + 2)`. -/
theorem submask_pairs_divisible (s : Nat) (hs : 2 ≤ s) :
    2 ^ (2 * s + 2) ∣ 2 ^ (s - 1) * 2 ^ (2 * s + 1) := by
  have hsplit : s - 1 = (s - 2) + 1 := by omega
  rw [hsplit, Nat.pow_succ]
  refine ⟨2 ^ (s - 2), ?_⟩
  have hpow : 2 ^ (2 * s + 2) = 2 ^ (2 * s + 1) * 2 := by
    rw [Nat.pow_succ]
  rw [hpow]
  simp only [Nat.mul_assoc, Nat.mul_comm]

end ConjectureLab.OeisA189286
