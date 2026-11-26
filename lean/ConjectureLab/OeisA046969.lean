/-
  OEIS A046969 (`conjecture1`): Denominators of B_{2n} / (2n(2n - 1))
  ===================================================================
  Formalizes the modular arithmetic core of the proof of A046969 (`conjecture1`):
  for every prime p > 3 such that 2p - 1 is also prime:
    1. p ≡ 1 (mod 6),
    2. 2p + 1 is divisible by 3 and > 3, hence composite (so 2p + 1 cannot
       contribute to den(B_{2p}) in the Von Staudt-Clausen theorem),
    3. 2p - 1 is coprime to 6 (hence coprime to 12),
    4. Exact reduced denominator checks for a(1), a(2), a(3).
-/

namespace ConjectureLab.OeisA046969

/-- Elementary primality predicate on `Nat`. -/
def IsPrime (n : Nat) : Prop :=
  1 < n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- A prime `p > 3` cannot be divisible by `2` or `3`. -/
theorem prime_gt3_not_dvd_2_3 (p : Nat) (hp : IsPrime p) (hgt : 3 < p) :
    p % 2 ≠ 0 ∧ p % 3 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro hmod
    have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.2 2 hdvd with h | h <;> omega
  · intro hmod
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.2 3 hdvd with h | h <;> omega

/-- If `p > 3` is prime and `2p - 1` is prime, then `p ≡ 1 (mod 6)`. -/
theorem prime_pair_mod_six (p : Nat) (hp : IsPrime p) (hgt : 3 < p)
    (hq : IsPrime (2 * p - 1)) : p % 6 = 1 := by
  have ⟨hp2, hp3⟩ := prime_gt3_not_dvd_2_3 p hp hgt
  have hqgt : 3 < 2 * p - 1 := by omega
  have ⟨_, hq3⟩ := prime_gt3_not_dvd_2_3 (2 * p - 1) hq hqgt
  have hp_eq : p = 6 * (p / 6) + p % 6 := (Nat.div_add_mod p 6).symm
  rcases (by omega : p % 6 = 0 ∨ p % 6 = 1 ∨ p % 6 = 2 ∨ p % 6 = 3 ∨ p % 6 = 4 ∨ p % 6 = 5) with
    h | h | h | h | h | h
  · exfalso; omega
  · exact h
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso
    have h2p : 2 * p - 1 = 3 * (4 * (p / 6) + 3) := by omega
    rw [h2p] at hq3
    omega

/-- Under the same hypotheses, `2p + 1` is divisible by `3` and `> 3`, hence composite. -/
theorem two_p_plus_one_composite (p : Nat) (hp : IsPrime p) (hgt : 3 < p)
    (hq : IsPrime (2 * p - 1)) : ¬ IsPrime (2 * p + 1) := by
  have hmod : p % 6 = 1 := prime_pair_mod_six p hp hgt hq
  intro hcomp
  have hdvd : 3 ∣ 2 * p + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  rcases hcomp.2 3 hdvd with h | h <;> omega

/-- Under the same hypotheses, `q = 2p - 1` is coprime to `12` (`q % 2 ≠ 0` and `q % 3 ≠ 0`). -/
theorem q_not_dvd_2_3 (p : Nat) (hp : IsPrime p) (hgt : 3 < p)
    (hq : IsPrime (2 * p - 1)) : (2 * p - 1) % 2 ≠ 0 ∧ (2 * p - 1) % 3 ≠ 0 := by
  have hmod : p % 6 = 1 := prime_pair_mod_six p hp hgt hq
  omega

/-- Reduced denominator of a fraction `num / den` (`den > 0`). -/
def reducedDen (num den : Nat) : Nat :=
  den / Nat.gcd num den

-- Exact verification of initial terms from B_2 = 1/6, B_4 = -1/30, B_6 = 1/42:
-- a(1) = den((1/6) / (2 * 1)) = den(1 / 12) = 12
-- a(2) = den((-1/30) / (4 * 3)) = den(-1 / 360) = 360
-- a(3) = den((1/42) / (6 * 5)) = den(1 / 1260) = 1260
theorem a_1_eq : reducedDen 1 (6 * 2 * 1) = 12 := rfl
theorem a_2_eq : reducedDen 1 (30 * 4 * 3) = 360 := rfl
theorem a_3_eq : reducedDen 1 (42 * 6 * 5) = 1260 := rfl

end ConjectureLab.OeisA046969
