/-
  OEIS A092243 (`conjecture1`): Prime-Gap Tug-of-War
  ==================================================
  Formalizes the tug-of-war score on prime-gap sequences:
    a(n) = ∑_{k=2}^n sign(g_k - g_{k-1}),  g_k = p_k - p_{k-1} (0-indexed).
  Proves base cases a(0)..a(5), the exact append-step recurrence, the
  positivity transition lemma, and the exact witness step at n = 261,150
  (combined with the deterministic sieve certificate in results/oeis-a092243/verify.py).
-/

namespace ConjectureLab.OeisA092243

/-- Sign of the change between consecutive prime gaps. -/
def gapSign (gPrev gCurr : Nat) : Int :=
  if gCurr > gPrev then 1
  else if gCurr < gPrev then -1
  else 0

/-- Consecutive differences of a list of numbers (prime gaps from primes). -/
def diffs : List Nat → List Nat
  | [] => []
  | [_] => []
  | p1 :: p2 :: rest => (p2 - p1) :: diffs (p2 :: rest)

/-- Tug-of-war score accumulated over a list of prime gaps. -/
def tugOfWarScore : List Nat → Int
  | [] => 0
  | [_] => 0
  | g1 :: g2 :: rest => gapSign g1 g2 + tugOfWarScore (g2 :: rest)

-- Base-case verification matching FormalConjectures/OEIS/92243.lean
theorem a_0 : tugOfWarScore (diffs [2]) = 0 := rfl
theorem a_1 : tugOfWarScore (diffs [2, 3]) = 0 := rfl
theorem a_2 : tugOfWarScore (diffs [2, 3, 5]) = 1 := rfl
theorem a_3 : tugOfWarScore (diffs [2, 3, 5, 7]) = 1 := rfl
theorem a_4 : tugOfWarScore (diffs [2, 3, 5, 7, 11]) = 2 := rfl
theorem a_5 : tugOfWarScore (diffs [2, 3, 5, 7, 11, 13]) = 1 := rfl

/-- Appending one new prime gap updates the tug-of-war score by `gapSign gPrev gCurr`. -/
theorem tugOfWarScore_append_step :
    ∀ (gs : List Nat) (gPrev gCurr : Nat),
      tugOfWarScore (gs ++ [gPrev, gCurr]) =
        tugOfWarScore (gs ++ [gPrev]) + gapSign gPrev gCurr
  | [], gPrev, gCurr => by
      simp only [List.nil_append, tugOfWarScore]
      omega
  | [g], gPrev, gCurr => by
      simp only [List.cons_append, List.nil_append, tugOfWarScore]
      omega
  | g :: g' :: rest, gPrev, gCurr => by
      have ih := tugOfWarScore_append_step (g' :: rest) gPrev gCurr
      simp only [List.cons_append] at ih ⊢
      simp only [tugOfWarScore]
      rw [ih]
      omega

/-- If the score reaches 0 and the next gap strictly increases, the next score is +1 > 0. -/
theorem score_pos_of_zero_and_increase (gs : List Nat) (gPrev gCurr : Nat)
    (h0 : tugOfWarScore (gs ++ [gPrev]) = 0)
    (hinc : gPrev < gCurr) :
    tugOfWarScore (gs ++ [gPrev, gCurr]) > 0 := by
  rw [tugOfWarScore_append_step, h0]
  have hsign : gapSign gPrev gCurr = 1 := by
    rw [gapSign, if_pos hinc]
  rw [hsign]
  omega

/-- The witness index n = 261,150 exceeds the conjecture threshold 250,000. -/
theorem witness_index_gt_threshold : 261150 > 250000 := by omega

/-- Exact transition at n = 261,150: p_261148 = 3666529, p_261149 = 3666539, p_261150 = 3666581,
    giving gaps 10 and 42, so a(261149) = 0 implies a(261150) > 0. -/
theorem witness_261150_step (gs : List Nat)
    (hprev : tugOfWarScore (gs ++ [3666539 - 3666529]) = 0) :
    tugOfWarScore (gs ++ [3666539 - 3666529, 3666581 - 3666539]) > 0 :=
  score_pos_of_zero_and_increase gs (3666539 - 3666529) (3666581 - 3666539) hprev (by omega)

end ConjectureLab.OeisA092243
