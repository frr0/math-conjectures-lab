namespace ConjectureLab.BrocardProblem

/-- Standard factorial on `Nat`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- All three known Brown number pairs satisfy `n! + 1 = m^2`. -/
theorem brocard_known_solutions :
    fact 4 + 1 = 5 * 5 ∧ fact 5 + 1 = 11 * 11 ∧ fact 7 + 1 = 71 * 71 :=
  ⟨rfl, rfl, rfl⟩

/-- For every `n ≥ 5`, `10` divides `n!`. -/
theorem ten_dvd_fact : ∀ n : Nat, 5 ≤ n → 10 ∣ fact n
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, h => by omega
  | 4, h => by omega
  | 5, _ => ⟨12, rfl⟩
  | n + 6, _ => by
    have ⟨k, hk⟩ := ten_dvd_fact (n + 5) (by omega)
    refine ⟨(n + 6) * k, ?_⟩
    show (n + 6) * fact (n + 5) = 10 * ((n + 6) * k)
    rw [hk, Nat.mul_left_comm]

/-- Universal last-digit obstruction: any solution to `n! + 1 = m^2` with `n ≥ 5`
    must end in decimal digit `1` or `9`. -/
theorem brocard_last_digit (n m : Nat) (hn : 5 ≤ n) (h : fact n + 1 = m * m) :
    m % 10 = 1 ∨ m % 10 = 9 := by
  have ⟨k, hk⟩ := ten_dvd_fact n hn
  have hmod : (m * m) % 10 = 1 := by omega
  rw [Nat.mul_mod] at hmod
  have hr : m % 10 < 10 := Nat.mod_lt m (by omega)
  match hval : m % 10 with
  | 0 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rw [hval] at hmod; omega
  | 1 => exact Or.inl rfl
  | 9 => exact Or.inr rfl
  | _ + 10 => omega

end ConjectureLab.BrocardProblem
