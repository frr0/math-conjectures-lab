/-
  OEIS A108864 — Complete Pure Lean 4 Disproof
  ============================================
  OEIS A108864 asks whether 1155 is the last odd positive integer with
  perfectDeficiency n ≤ 10 (where perfectDeficiency n is the remainder after
  greedily subtracting divisors of n in increasing order).

  We prove (100% inside the Lean 4 kernel, zero Mathlib, zero sorry, zero
  custom axioms) that:
    m = 815634435 = 3 * 5 * 7 * 11 * 547 * 1291
  is odd, strictly greater than 1155, and satisfies perfectDeficiency m = 6 ≤ 10.
-/

namespace ConjectureLab.OeisA108864

/-- Greedy step used in the definition of perfect deficiency (OEIS A109883). -/
def pdStep (n acc d : Nat) : Nat :=
  if d ∣ n ∧ d ≤ acc then acc - d else acc

/-- Perfect deficiency of `n` (exact match with `FormalConjectures/OEIS/108864.lean`). -/
def perfectDeficiency (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (pdStep n) n

/-- Sum of a list of natural numbers (self-contained for pure Lean 4 core). -/
def listSum : List Nat → Nat
  | [] => 0
  | a :: as => a + listSum as

/-- Duplicate-free predicate on `List Nat`. -/
def NoDup : List Nat → Prop
  | [] => True
  | a :: as => a ∉ as ∧ NoDup as

/-- Computable duplicate-free checker. -/
def noDupB : List Nat → Bool
  | [] => true
  | a :: as => !(as.elem a) && noDupB as

theorem not_mem_of_elem_false {a : Nat} : ∀ {l : List Nat}, l.elem a = false → a ∉ l
  | [], _ => fun h => nomatch h
  | x :: xs, h => by
      simp only [List.elem_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      intro hmem
      cases hmem with
      | head => exact h.1 rfl
      | tail _ htail => exact not_mem_of_elem_false h.2 htail

theorem noDup_of_noDupB : ∀ {l : List Nat}, noDupB l = true → NoDup l
  | [], _ => trivial
  | a :: as, h => by
      simp only [noDupB, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact ⟨not_mem_of_elem_false h.1, noDup_of_noDupB h.2⟩

/-- Primality predicate. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- Bounded trial-division primality certificate. -/
def noDivisorRange (p d : Nat) : Nat → Bool
  | 0 => true
  | f + 1 =>
    if d * d > p then true
    else if p % d == 0 then false
    else noDivisorRange p (d + 1) f

theorem noDivisorRange_sound {p : Nat} :
    ∀ (fuel d : Nat),
      (d + fuel) * (d + fuel) > p →
      noDivisorRange p d fuel = true →
      ∀ k : Nat, d ≤ k → k * k ≤ p → ¬ (k ∣ p)
  | 0, d, hbound, _, k, hdk, hkk, _ => by
      have hle : d * d ≤ k * k := Nat.mul_le_mul hdk hdk
      simp only [Nat.add_zero] at hbound
      omega
  | f + 1, d, hbound, hcheck, k, hdk, hkk, hdvd => by
      unfold noDivisorRange at hcheck
      by_cases hgt : d * d > p
      · have hle : d * d ≤ k * k := Nat.mul_le_mul hdk hdk
        omega
      · rw [if_neg hgt] at hcheck
        by_cases hmod : (p % d == 0) = true
        · rw [if_pos hmod] at hcheck
          cases hcheck
        · rw [if_neg hmod] at hcheck
          by_cases hkd : k = d
          · subst hkd
            have hm0 : p % k = 0 := Nat.mod_eq_zero_of_dvd hdvd
            exact hmod (by simp [hm0])
          · have hbound' : ((d + 1) + f) * ((d + 1) + f) > p := by
              have : d + 1 + f = d + (f + 1) := by omega
              rw [this]
              exact hbound
            exact noDivisorRange_sound f (d + 1) hbound' hcheck k (by omega) hkk hdvd

theorem isPrime_of_noDivisor {p fuel : Nat}
    (hp : 2 ≤ p)
    (hbound : (2 + fuel) * (2 + fuel) > p)
    (hcheck : noDivisorRange p 2 fuel = true) :
    IsPrime p := by
  refine ⟨hp, fun d hdvd => ?_⟩
  have ⟨q, hq⟩ := hdvd
  by_cases hd0 : d = 0
  · subst hd0; simp at hq; omega
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  by_cases hdp : d = p
  · exact Or.inr hdp
  have hq_dvd : q ∣ p := ⟨d, by rw [Nat.mul_comm]; exact hq⟩
  have hq2 : 2 ≤ q := by
    by_cases hq0 : q = 0
    · subst hq0; simp at hq; omega
    by_cases hq1 : q = 1
    · subst hq1; simp at hq; exact absurd hq.symm hdp
    omega
  have hd2 : 2 ≤ d := by omega
  by_cases hle : d ≤ q
  · have hdd : d * d ≤ p := by
      rw [hq]
      exact Nat.mul_le_mul_left d hle
    exact False.elim (noDivisorRange_sound fuel 2 hbound hcheck d hd2 hdd hdvd)
  · have hqq : q * q ≤ p := by
      rw [hq, Nat.mul_comm]
      exact Nat.mul_le_mul_left q (by omega)
    exact False.elim (noDivisorRange_sound fuel 2 hbound hcheck q hq2 hqq hq_dvd)

/-- Euclid's lemma: any divisor of `p * b` (with `p` prime) either is `p * a'` with `a' ∣ b`, or divides `b`. -/
theorem dvd_mul_of_prime {p a b : Nat} (hp : IsPrime p) (h : a ∣ p * b) :
    (∃ a', a = p * a' ∧ a' ∣ b) ∨ a ∣ b := by
  have hgp : Nat.gcd a p ∣ p := Nat.gcd_dvd_right a p
  have hga : Nat.gcd a p ∣ a := Nat.gcd_dvd_left a p
  cases hp.2 (Nat.gcd a p) hgp with
  | inl h1 =>
    exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  | inr heq =>
    rw [heq] at hga
    have ⟨a', ha'⟩ := hga
    rw [ha'] at h
    have ⟨c, hc⟩ := h
    have hb : b = a' * c := by
      apply Nat.mul_left_cancel (show 0 < p by have := hp.1; omega)
      rw [hc, Nat.mul_assoc]
    exact Or.inl ⟨a', ha', ⟨c, hb⟩⟩

/-- Product of a list of natural numbers. -/
def listProd : List Nat → Nat
  | [] => 1
  | p :: ps => p * listProd ps

/-- All subset products of a list of primes (the exact list of divisors when primes are distinct). -/
def subProds : List Nat → List Nat
  | [] => [1]
  | p :: ps => subProds ps ++ (subProds ps).map (p * ·)

theorem mem_subProds_of_dvd :
    ∀ (ps : List Nat), (∀ p ∈ ps, IsPrime p) → ∀ d, d ∣ listProd ps → d ∈ subProds ps
  | [], _, d, hd => by
      simp only [listProd] at hd
      have hd1 : d = 1 := Nat.eq_one_of_dvd_one hd
      subst hd1
      simp [subProds]
  | p :: ps, hps, d, hd => by
      simp only [listProd] at hd
      have hp : IsPrime p := hps p (List.mem_cons_self p ps)
      have hps' : ∀ q ∈ ps, IsPrime q := fun q hq => hps q (List.mem_cons_of_mem p hq)
      simp only [subProds, List.mem_append, List.mem_map]
      cases dvd_mul_of_prime hp hd with
      | inl h =>
        have ⟨d', hd', hd'dvd⟩ := h
        exact Or.inr ⟨d', mem_subProds_of_dvd ps hps' d' hd'dvd, hd'.symm⟩
      | inr hdvd =>
        exact Or.inl (mem_subProds_of_dvd ps hps' d hdvd)

theorem dvd_of_mem_subProds :
    ∀ (ps : List Nat) (d : Nat), d ∈ subProds ps → d ∣ listProd ps
  | [], d, hd => by
      simp only [subProds, List.mem_singleton] at hd
      subst hd
      exact Nat.dvd_refl 1
  | p :: ps, d, hd => by
      simp only [subProds, List.mem_append, List.mem_map] at hd
      simp only [listProd]
      cases hd with
      | inl h =>
        have hdvd := dvd_of_mem_subProds ps d h
        have ⟨c, hc⟩ := hdvd
        exact ⟨p * c, by rw [hc, Nat.mul_left_comm]⟩
      | inr h =>
        have ⟨d', hd'mem, hd'eq⟩ := h
        subst hd'eq
        have ⟨c, hc⟩ := dvd_of_mem_subProds ps d' hd'mem
        exact ⟨c, by rw [hc, Nat.mul_assoc]⟩

-- Helper lemmas relating `listSum` and filtering by `< k`.
theorem listSum_filter_le (p : Nat → Bool) :
    ∀ (l : List Nat), listSum (l.filter p) ≤ listSum l
  | [] => Nat.le_refl 0
  | a :: as => by
      have ih := listSum_filter_le p as
      simp only [List.filter_cons, listSum]
      cases p a <;> simp only [listSum] <;> omega

theorem listSum_filter_lt_succ_of_not_mem (k : Nat) :
    ∀ {l : List Nat}, k ∉ l →
      listSum (l.filter (fun x => decide (x < k + 1))) =
        listSum (l.filter (fun x => decide (x < k)))
  | [], _ => rfl
  | a :: as, hnot => by
      have hne : a ≠ k := fun h => hnot (h ▸ List.mem_cons_self a as)
      have hnot' : k ∉ as := fun h => hnot (List.mem_cons_of_mem a h)
      have ih := listSum_filter_lt_succ_of_not_mem k hnot'
      have hdec : decide (a < k + 1) = decide (a < k) := by
        by_cases h : a < k
        · have h' : a < k + 1 := by omega
          simp [h, h']
        · have h' : ¬ (a < k + 1) := by omega
          simp [h, h']
      simp only [List.filter_cons, hdec]
      cases decide (a < k) <;> simp only [listSum] <;> omega

theorem listSum_filter_lt_succ_of_mem (k : Nat) :
    ∀ {l : List Nat}, NoDup l → k ∈ l →
      listSum (l.filter (fun x => decide (x < k + 1))) =
        listSum (l.filter (fun x => decide (x < k))) + k
  | [], _, hmem => nomatch hmem
  | a :: as, ⟨hnot, hnd⟩, hmem => by
      cases hmem with
      | head =>
        have h1 : decide (a < a + 1) = true := by simp
        have h2 : decide (a < a) = false := by simp
        have ih := listSum_filter_lt_succ_of_not_mem a hnot
        simp only [List.filter_cons, h1, h2, listSum]
        omega
      | tail _ htail =>
        have hne : a ≠ k := fun h => hnot (h ▸ htail)
        have ih := listSum_filter_lt_succ_of_mem k hnd htail
        have hdec : decide (a < k + 1) = decide (a < k) := by
          by_cases h : a < k
          · have h' : a < k + 1 := by omega
            simp [h, h']
          · have h' : ¬ (a < k + 1) := by omega
            simp [h, h']
        simp only [List.filter_cons, hdec]
        cases decide (a < k) <;> simp only [listSum] <;> omega

theorem filter_eq_self_of_forall {p : Nat → Bool} :
    ∀ {l : List Nat}, (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | a :: as, h => by
      have ha : p a = true := h a (List.mem_cons_self a as)
      have has : ∀ x ∈ as, p x = true := fun x hx => h x (List.mem_cons_of_mem a hx)
      simp only [List.filter_cons, ha, filter_eq_self_of_forall has]

/-- Invariant for `foldl (pdStep n) n (List.range k)` when `divs` is the exact duplicate-free
    list of proper divisors of a deficient number `n`. -/
theorem foldl_range_eq_sub_filter_sum (n : Nat) (divs : List Nat)
    (hnd : NoDup divs)
    (hmem : ∀ d, d < n → (d ∣ n ↔ d ∈ divs))
    (hsum : listSum divs ≤ n) :
    ∀ k, k ≤ n →
      (List.range k).foldl (pdStep n) n =
        n - listSum (divs.filter (fun x => decide (x < k)))
  | 0, _ => by
      have hzero : ∀ l : List Nat, listSum (l.filter (fun x => decide (x < 0))) = 0 := by
        intro l
        induction l with
        | nil => rfl
        | cons x xs ih =>
          have : decide (x < 0) = false := by simp
          simp only [List.filter_cons, this, ih]
      simp [hzero]
  | k + 1, hk => by
      have ih := foldl_range_eq_sub_filter_sum n divs hnd hmem hsum k (by omega)
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, pdStep]
      by_cases hdvd : k ∣ n
      · have hkmem : k ∈ divs := (hmem k (by omega)).mp hdvd
        have hstep := listSum_filter_lt_succ_of_mem k hnd hkmem
        have hle_total : listSum (divs.filter (fun x => decide (x < k + 1))) ≤ n :=
          Nat.le_trans (listSum_filter_le _ divs) hsum
        have hk_le : k ≤ n - listSum (divs.filter (fun x => decide (x < k))) := by omega
        rw [if_pos ⟨hdvd, hk_le⟩]
        omega
      · have hknot : k ∉ divs := fun h => hdvd ((hmem k (by omega)).mpr h)
        have hstep := listSum_filter_lt_succ_of_not_mem k hknot
        rw [if_neg (fun h => hdvd h.1)]
        omega

/-- For any deficient number `n` whose proper divisors are `divs` (with `0 < listSum divs ≤ n`),
    `perfectDeficiency n = n - listSum divs`. -/
theorem perfectDeficiency_eq_sub_sum (n : Nat) (divs : List Nat)
    (hnd : NoDup divs)
    (hmem : ∀ d, d < n → (d ∣ n ↔ d ∈ divs))
    (hlt : ∀ d ∈ divs, d < n)
    (hpos : 0 < listSum divs)
    (hsum : listSum divs ≤ n) :
    perfectDeficiency n = n - listSum divs := by
  unfold perfectDeficiency
  rw [List.range_succ, List.foldl_append]
  rw [foldl_range_eq_sub_filter_sum n divs hnd hmem hsum n (Nat.le_refl n)]
  have hfilt : divs.filter (fun x => decide (x < n)) = divs :=
    filter_eq_self_of_forall (fun x hx => by simp [hlt x hx])
  rw [hfilt]
  simp only [List.foldl_cons, List.foldl_nil, pdStep]
  have hnotle : ¬ (n ≤ n - listSum divs) := by omega
  rw [if_neg (fun h => hnotle h.2)]

-- ============================================================================
-- Concrete Counterexample: m = 815634435 = 3 * 5 * 7 * 11 * 547 * 1291
-- ============================================================================

def counterexamplePrimes : List Nat := [3, 5, 7, 11, 547, 1291]

def counterexampleN : Nat := 815634435

def properDivs : List Nat :=
  (subProds counterexamplePrimes).filter (fun d => decide (d < counterexampleN))

theorem listProd_counterexamplePrimes : listProd counterexamplePrimes = counterexampleN := rfl

theorem prime_3 : IsPrime 3 := isPrime_of_noDivisor (fuel := 2) (by omega) (by omega) rfl
theorem prime_5 : IsPrime 5 := isPrime_of_noDivisor (fuel := 2) (by omega) (by omega) rfl
theorem prime_7 : IsPrime 7 := isPrime_of_noDivisor (fuel := 2) (by omega) (by omega) rfl
theorem prime_11 : IsPrime 11 := isPrime_of_noDivisor (fuel := 3) (by omega) (by omega) rfl
theorem prime_547 : IsPrime 547 := isPrime_of_noDivisor (fuel := 25) (by omega) (by omega) rfl
theorem prime_1291 : IsPrime 1291 := isPrime_of_noDivisor (fuel := 36) (by omega) (by omega) rfl

theorem all_counterexample_primes : ∀ p ∈ counterexamplePrimes, IsPrime p := by
  intro p hp
  simp only [counterexamplePrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  cases hp with
  | inl h => subst h; exact prime_3
  | inr hp => cases hp with
    | inl h => subst h; exact prime_5
    | inr hp => cases hp with
      | inl h => subst h; exact prime_7
      | inr hp => cases hp with
        | inl h => subst h; exact prime_11
        | inr hp => cases hp with
          | inl h => subst h; exact prime_547
          | inr h => subst h; exact prime_1291

theorem properDivs_noDup : NoDup properDivs :=
  noDup_of_noDupB rfl

theorem properDivs_sum : listSum properDivs = 815634429 := rfl

theorem properDivs_lt : ∀ d ∈ properDivs, d < counterexampleN := by
  intro d hd
  simp only [properDivs, List.mem_filter, decide_eq_true_eq] at hd
  exact hd.2

theorem properDivs_iff (d : Nat) (hd : d < counterexampleN) :
    d ∣ counterexampleN ↔ d ∈ properDivs := by
  constructor
  · intro hdvd
    rw [← listProd_counterexamplePrimes] at hdvd
    have hmem := mem_subProds_of_dvd counterexamplePrimes all_counterexample_primes d hdvd
    simp only [properDivs, List.mem_filter, decide_eq_true_eq]
    exact ⟨hmem, hd⟩
  · intro hmem
    simp only [properDivs, List.mem_filter, decide_eq_true_eq] at hmem
    rw [← listProd_counterexamplePrimes]
    exact dvd_of_mem_subProds counterexamplePrimes d hmem.1

/-- Exact kernel-verified evaluation: `perfectDeficiency 815634435 = 6`. -/
theorem perfectDeficiency_815634435 : perfectDeficiency 815634435 = 6 := by
  change perfectDeficiency counterexampleN = 6
  rw [perfectDeficiency_eq_sub_sum counterexampleN properDivs
    properDivs_noDup properDivs_iff properDivs_lt
    (by rw [properDivs_sum]; omega)
    (by rw [properDivs_sum]; decide)]
  rw [properDivs_sum]
  rfl

/-- Main theorem: `815634435` is an odd integer strictly greater than `1155` with
    `perfectDeficiency ≤ 10`, disproving the OEIS A108864 conjecture that `1155`
    is the last odd term. -/
theorem disproves_a108864_odd_bound :
    ∃ m : Nat, m > 1155 ∧ m % 2 = 1 ∧ perfectDeficiency m ≤ 10 := by
  refine ⟨815634435, by omega, rfl, ?_⟩
  rw [perfectDeficiency_815634435]
  omega

end ConjectureLab.OeisA108864
