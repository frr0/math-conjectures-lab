namespace ConjectureLab.ErdosStraus

/-- Cross-multiplied Erdős–Straus predicate: `4 / n = 1 / x + 1 / y + 1 / z`
    for positive natural numbers `x, y, z`. -/
def HasErdosStraus (n : Nat) : Prop :=
  ∃ x y z : Nat, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

/-- Case 1: every even `n = 2 * k` with `k ≥ 1`. -/
theorem erdos_straus_even (k : Nat) (hk : 0 < k) : HasErdosStraus (2 * k) := by
  refine ⟨k, 2 * k, 2 * k, hk, by omega, by omega, ?_⟩
  have h1 : (2 * k) * (2 * k) = 4 * (k * k) := by
    calc (2 * k) * (2 * k) = 2 * (k * (2 * k)) := by rw [Nat.mul_assoc]
      _ = 2 * (2 * (k * k)) := by rw [Nat.mul_left_comm k 2 k]
      _ = 4 * (k * k) := by omega
  have h2 : k * (2 * k) = 2 * (k * k) := by rw [Nat.mul_left_comm]
  have h3 : (2 * k) * (2 * k) + k * (2 * k) + k * (2 * k) = 8 * (k * k) := by
    rw [h1, h2]; omega
  rw [h3]
  calc 4 * k * (2 * k) * (2 * k)
      = 4 * k * ((2 * k) * (2 * k)) := by rw [Nat.mul_assoc (4 * k)]
    _ = 4 * k * (4 * (k * k)) := by rw [h1]
    _ = 4 * (k * (4 * (k * k))) := by rw [Nat.mul_assoc]
    _ = 4 * (4 * (k * (k * k))) := by rw [Nat.mul_left_comm k 4 (k * k)]
    _ = 2 * (8 * (k * (k * k))) := by omega
    _ = 2 * (k * (8 * (k * k))) := by rw [Nat.mul_left_comm 8 k (k * k)]
    _ = (2 * k) * (8 * (k * k)) := by rw [Nat.mul_assoc]

/-- Case 2: every `n = 4 * k + 3`. -/
theorem erdos_straus_three_mod_four (k : Nat) : HasErdosStraus (4 * k + 3) := by
  let m := k + 1
  let n := 4 * k + 3
  let y := 2 * m * n
  have hm : 0 < m := by omega
  have hn : 0 < n := by omega
  have hy : 0 < y := Nat.mul_pos (Nat.mul_pos (by omega) hm) hn
  refine ⟨m, y, y, hm, hy, hy, ?_⟩
  have hmn : n + 1 = 4 * m := by omega
  have hsum : y + m + m = 8 * (m * m) := by
    calc y + m + m = 2 * m * n + (m + m) := by rw [Nat.add_assoc]
      _ = 2 * m * n + 2 * m * 1 := by omega
      _ = 2 * m * (n + 1) := by rw [← Nat.mul_add]
      _ = 2 * m * (4 * m) := by rw [hmn]
      _ = 2 * (m * (4 * m)) := by rw [Nat.mul_assoc]
      _ = 2 * (4 * (m * m)) := by rw [Nat.mul_left_comm m 4 m]
      _ = 8 * (m * m) := by omega
  have hcore : 4 * m * y = n * (y + m + m) := by
    rw [hsum]
    calc 4 * m * (2 * m * n) = 4 * (m * (2 * (m * n))) := by
          rw [Nat.mul_assoc 4 m, Nat.mul_assoc 2 m n]
      _ = 4 * (2 * (m * (m * n))) := by rw [Nat.mul_left_comm m 2 (m * n)]
      _ = 8 * (m * (m * n)) := by omega
      _ = 8 * (m * (n * m)) := by rw [Nat.mul_comm m n]
      _ = 8 * (n * (m * m)) := by rw [Nat.mul_left_comm m n m]
      _ = n * (8 * (m * m)) := by rw [Nat.mul_left_comm]
  calc 4 * m * y * y = (n * (y + m + m)) * y := by rw [hcore]
    _ = n * ((y + m + m) * y) := by rw [Nat.mul_assoc]
    _ = n * (y * y + m * y + m * y) := by rw [Nat.add_mul, Nat.add_mul]

/-- Case 3: every `n = 8 * k + 5`. -/
theorem erdos_straus_five_mod_eight (k : Nat) : HasErdosStraus (8 * k + 5) := by
  let m := k + 1
  let n := 8 * k + 5
  let z := m * n
  have hm : 0 < m := by omega
  have hn : 0 < n := by omega
  have hz : 0 < z := Nat.mul_pos hm hn
  refine ⟨2 * m, 2 * z, z, by omega, by omega, hz, ?_⟩
  have hmn : n + 3 = 8 * m := by omega
  have hsum : 2 * z + 2 * m + 4 * m = 16 * (m * m) := by
    calc 2 * z + 2 * m + 4 * m = 2 * (m * n) + (2 * m + 4 * m) := by rw [Nat.add_assoc]
      _ = 2 * m * n + 2 * m * 3 := by
        rw [← Nat.mul_assoc 2 m n]
        omega
      _ = 2 * m * (n + 3) := by rw [← Nat.mul_add]
      _ = 2 * m * (8 * m) := by rw [hmn]
      _ = 2 * (m * (8 * m)) := by rw [Nat.mul_assoc]
      _ = 2 * (8 * (m * m)) := by rw [Nat.mul_left_comm m 8 m]
      _ = 16 * (m * m) := by omega
  have hcore : 4 * (2 * m) * (2 * z) = n * (2 * z + 2 * m + 4 * m) := by
    rw [hsum]
    calc 4 * (2 * m) * (2 * z)
        = (4 * 2) * m * (2 * z) := by rw [← Nat.mul_assoc 4 2 m]
      _ = 8 * (m * (2 * z)) := by rw [Nat.mul_assoc]
      _ = 8 * (2 * (m * z)) := by rw [Nat.mul_left_comm m 2 z]
      _ = 16 * (m * (m * n)) := by omega
      _ = 16 * (m * (n * m)) := by rw [Nat.mul_comm m n]
      _ = 16 * (n * (m * m)) := by rw [Nat.mul_left_comm m n m]
      _ = n * (16 * (m * m)) := by rw [Nat.mul_left_comm]
  have h2mz : 2 * m * (2 * z) = 4 * m * z := by
    calc 2 * m * (2 * z) = 2 * (m * (2 * z)) := by rw [Nat.mul_assoc]
      _ = 2 * (2 * (m * z)) := by rw [Nat.mul_left_comm m 2 z]
      _ = 4 * (m * z) := by omega
      _ = 4 * m * z := by rw [← Nat.mul_assoc]
  calc 4 * (2 * m) * (2 * z) * z
      = (n * (2 * z + 2 * m + 4 * m)) * z := by rw [hcore]
    _ = n * ((2 * z + 2 * m + 4 * m) * z) := by rw [Nat.mul_assoc]
    _ = n * (2 * z * z + 2 * m * z + 4 * m * z) := by rw [Nat.add_mul, Nat.add_mul]
    _ = n * (2 * z * z + 2 * m * z + 2 * m * (2 * z)) := by rw [h2mz]

/-- Master partial theorem: Erdős–Straus holds for every `n ≥ 2` with `n % 8 ≠ 1`
    (covering 7 out of 8 residue classes modulo 8). -/
theorem erdos_straus_not_one_mod_eight (n : Nat) (hn : 2 ≤ n) (hmod : n % 8 ≠ 1) :
    HasErdosStraus n := by
  by_cases heven : n % 2 = 0
  · have hEq : n = 2 * (n / 2) := by omega
    rw [hEq]
    exact erdos_straus_even (n / 2) (by omega)
  · by_cases h3 : n % 4 = 3
    · have hEq : n = 4 * (n / 4) + 3 := by omega
      rw [hEq]
      exact erdos_straus_three_mod_four (n / 4)
    · have hEq : n = 8 * (n / 8) + 5 := by omega
      rw [hEq]
      exact erdos_straus_five_mod_eight (n / 8)

end ConjectureLab.ErdosStraus
