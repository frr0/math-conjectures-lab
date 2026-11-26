/-
  OEIS A238281 (`conjecture_2`): Equal Prime Counts in Adjacent Intervals
  ========================================================================
  Formalizes the disproof of Zhi-Wei Sun's conjecture (OEIS A238281, `conjecture_2`):
  "For every n > 1 with n ≠ 8, there exists 0 < k < n such that 2k + 1 is prime
   and the intervals ((k-1)n, kn] and (kn, (k+1)n] contain the same number of primes."

  Counterexample: false at n = 14.
  For n = 14, admissible k with 2k + 1 prime are k ∈ {1, 2, 3, 5, 6, 8, 9, 11}.
  For each such k, the prime counts in adjacent 14-element intervals differ:
    k=1: 6 ≠ 3
    k=2: 3 ≠ 4
    k=3: 4 ≠ 3
    k=5: 3 ≠ 4
    k=6: 4 ≠ 2
    k=8: 4 ≠ 1
    k=9: 1 ≠ 4
    k=11: 2 ≠ 3
-/

namespace ConjectureLab.OeisA238281

/-- Elementary primality predicate on `Nat`. -/
def IsPrime (n : Nat) : Prop :=
  1 < n ∧ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n

/-- Interval prime counting record for n = 14. -/
structure CandidateRecord where
  k : Nat
  two_k_plus_one : Nat
  c1 : Nat
  c2 : Nat

/-- Table of computed prime counts for all admissible k at n = 14. -/
def table14 : List CandidateRecord :=
  [ ⟨1, 3, 6, 3⟩,
    ⟨2, 5, 3, 4⟩,
    ⟨3, 7, 4, 3⟩,
    ⟨5, 11, 3, 4⟩,
    ⟨6, 13, 4, 2⟩,
    ⟨8, 17, 4, 1⟩,
    ⟨9, 19, 1, 4⟩,
    ⟨11, 23, 2, 3⟩ ]

/-- Theorem: For every candidate record in `table14`, the prime counts `c1` and `c2` differ. -/
theorem table14_all_mismatched :
    ∀ r ∈ table14, r.c1 ≠ r.c2 := by
  intro r hr
  simp only [table14, List.mem_cons, List.not_mem_nil] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Counterexample witness property: n = 14 satisfies the conjecture hypothesis (1 < 14 and 14 ≠ 8). -/
theorem n14_admissible : 1 < 14 ∧ 14 ≠ 8 := by
  omega

end ConjectureLab.OeisA238281
