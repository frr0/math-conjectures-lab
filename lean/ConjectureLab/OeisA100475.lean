namespace ConjectureLab.OeisA100475

/-- Iterated orbit `orbit f x n = f^[n](x)`. -/
def orbit (f : Nat → Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => f (orbit f x n)

/-- Ultimate periodicity predicate matching `FormalConjectures/OEIS/100475.lean`. -/
def IsUltimatelyPeriodic (g : Nat → Nat) : Prop :=
  ∃ N P : Nat, 0 < P ∧ ∀ n : Nat, N ≤ n → g (n + P) = g n

/-- Once an orbit enters the strictly-increasing region `[K, ∞)`, it stays there forever. -/
theorem orbit_stays_above (f : Nat → Nat) (K : Nat)
    (hinc : ∀ k : Nat, K ≤ k → k < f k)
    (x m : Nat) (hm : K ≤ orbit f x m) :
    ∀ t : Nat, K ≤ orbit f x (m + t)
  | 0 => hm
  | t + 1 => by
    have ih := orbit_stays_above f K hinc x m hm t
    have hlt := hinc (orbit f x (m + t)) ih
    show K ≤ f (orbit f x (m + t))
    omega

/-- In the strictly-increasing region `[K, ∞)`, every positive step strictly increases the orbit. -/
theorem orbit_strict_step (f : Nat → Nat) (K : Nat)
    (hinc : ∀ k : Nat, K ≤ k → k < f k)
    (x m : Nat) (hm : K ≤ orbit f x m) :
    ∀ d : Nat, orbit f x m < orbit f x (m + (d + 1))
  | 0 => hinc (orbit f x m) hm
  | d + 1 => by
    have ih := orbit_strict_step f K hinc x m hm d
    have habove := orbit_stays_above f K hinc x m hm (d + 1)
    have hstep := hinc (orbit f x (m + (d + 1))) habove
    show orbit f x m < f (orbit f x (m + (d + 1)))
    omega

/-- Escape theorem: if `f` is strictly increasing on `[K, ∞)` and the orbit of `x`
    eventually reaches `[K, ∞)`, then the orbit is NOT ultimately periodic. -/
theorem not_periodic_of_escape (f : Nat → Nat) (K : Nat)
    (hinc : ∀ k : Nat, K ≤ k → k < f k)
    (x : Nat) (hescape : ∃ m : Nat, K ≤ orbit f x m) :
    ¬ IsUltimatelyPeriodic (orbit f x) := by
  intro ⟨N, P, hP, hper⟩
  have ⟨m, hm⟩ := hescape
  let M := max m N
  have hMm : m ≤ M := Nat.le_max_left m N
  have hMN : N ≤ M := Nat.le_max_right m N
  have hMeq : M = m + (M - m) := by omega
  have hKM : K ≤ orbit f x M := by
    rw [hMeq]
    exact orbit_stays_above f K hinc x m hm (M - m)
  have hPeq : P = (P - 1) + 1 := by omega
  have hlt : orbit f x M < orbit f x (M + P) := by
    rw [hPeq]
    exact orbit_strict_step f K hinc x M hKM (P - 1)
  have heq : orbit f x (M + P) = orbit f x M := hper M hMN
  omega

/-- Digit-reversal lower bound: if a number `p` has `D` decimal digits (`p < 10^D`),
    its reversal has at least `D` digits (`10^(D-1) ≤ rev`), and `10 * k ≤ p`, then `k < rev`. -/
theorem step_gt_of_ten_mul (k p rev D : Nat) (hD : 1 ≤ D)
    (hp_upper : p < 10 ^ D) (hrev_lower : 10 ^ (D - 1) ≤ rev) (h10 : 10 * k ≤ p) :
    k < rev := by
  have hDeq : D = (D - 1) + 1 := by omega
  have hpow : 10 ^ D = 10 * 10 ^ (D - 1) := by
    calc 10 ^ D = 10 ^ ((D - 1) + 1) := by rw [← hDeq]
      _ = 10 ^ (D - 1) * 10 := Nat.pow_succ 10 (D - 1)
      _ = 10 * 10 ^ (D - 1) := Nat.mul_comm _ _
  omega

end ConjectureLab.OeisA100475
