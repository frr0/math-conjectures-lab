namespace ConjectureLab.OeisA189409

/-- `n` is squarefree if no integer `d > 1` satisfies `d * d ∣ n`. -/
def IsSquarefree (n : Nat) : Prop :=
  ∀ d : Nat, d * d ∣ n → d = 1

/-- The 9-th primorial `p_9# = 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23`. -/
def primorial9 : Nat := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23

/-- `a(9) = (p_9#)^2 + 1`. -/
def a9 : Nat := primorial9 * primorial9 + 1

/-- Exact divisibility witness: `29^2 = 841` divides `(p_9#)^2 + 1`. -/
theorem dvd_a9 : 29 * 29 ∣ a9 :=
  ⟨59180057841661, rfl⟩

/-- Complete disproof of OEIS A189409 (`conjecture_1`): `(p_9#)^2 + 1` is NOT squarefree. -/
theorem not_squarefree_a9 : ¬ IsSquarefree a9 := by
  intro hsf
  have h29 : 29 = 1 := hsf 29 dvd_a9
  omega

end ConjectureLab.OeisA189409
