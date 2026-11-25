namespace ConjectureLab.EulerFifthPowers

/-- Lander & Parkin (1966) counterexample to Euler's sum of powers conjecture for k = 5:
    there exist positive integers a, b, c, d, e such that a^5 + b^5 + c^5 + d^5 = e^5. -/
theorem euler_fifth_powers_counterexample :
    ∃ a b c d e : Nat,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
      a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 = e ^ 5 :=
  ⟨27, 84, 110, 133, 144,
    Nat.zero_lt_succ 26,
    Nat.zero_lt_succ 83,
    Nat.zero_lt_succ 109,
    Nat.zero_lt_succ 132,
    Nat.zero_lt_succ 143,
    rfl⟩

end ConjectureLab.EulerFifthPowers
