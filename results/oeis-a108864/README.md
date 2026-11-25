# OEIS A108864 — Last Odd Term with Perfect Deficiency $\le 10$

## Conjecture Statement
For a positive integer $n$, the **perfect deficiency** of $n$ (OEIS A109883) is the remainder obtained by starting with $n$ and greedily subtracting each divisor $d \mid n$ in increasing order $1, \dots, n$, skipping any divisor larger than the current remainder:

$$\mathrm{perfectDeficiency}(n) = \mathrm{foldl}\!\left(\lambda m\, d \Rightarrow \text{if } d \mid n \land d \le m \text{ then } m - d \text{ else } m,\; n,\; [0, 1, \dots, n]\right).$$

OEIS A108864 consists of all positive integers $n$ with $\mathrm{perfectDeficiency}(n) \le 10$. In `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/108864.lean`), the open question asks:

> **Question (`OeisA108864.conjecture`):** Is $1155$ the last odd number in this sequence? (Equivalently, is every term $a(n)$ with $n > 58$ even?)

## Outcome
**Disproved (✅ 100% Lean 4 kernel-verified counterexample).**

The odd integer
$$m = 815{,}634{,}435 = 3 \times 5 \times 7 \times 11 \times 547 \times 1291 > 1155$$
satisfies:
- $m \equiv 1 \pmod 2$ (odd);
- $m$ is squarefree with 6 prime factors, hence has exactly $2^6 = 64$ divisors;
- $\sigma(m) = 4 \cdot 6 \cdot 8 \cdot 12 \cdot 548 \cdot 1292 = 1{,}631{,}268{,}864$;
- the sum of all proper divisors of $m$ is $\sigma(m) - m = 815{,}634{,}429 = m - 6 < m$;
- therefore, every proper divisor $d < m$ is subtracted during the greedy fold and $d = m$ is skipped (since $m > 6$), yielding:
$$\mathrm{perfectDeficiency}(815{,}634{,}435) = 6 \le 10.$$

Hence $815{,}634{,}435$ is an odd member of OEIS A108864 strictly greater than $1155$, refuting the conjecture that $1155$ is the last odd term.

## Literature Check
- Source: [OEIS A108864](https://oeis.org/A108864) and `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/108864.lean`), where the question is currently marked `research open, question`.
- The counterexample $815{,}634{,}435$ also appears in the related deficiency-6 sequences [OEIS A087485](https://oeis.org/A087485) and [OEIS A141548](https://oeis.org/A141548), since any odd deficient number with $2m - \sigma(m) = 6$ automatically has $\mathrm{perfectDeficiency}(m) = 6 \le 10$.

## Verification
- **Lean 4 ([OeisA108864.lean](../../lean/ConjectureLab/OeisA108864.lean)):** Complete, self-contained pure Lean 4 proof (zero Mathlib, zero `sorry`, zero custom axioms) proving:
  1. Primality of $3, 5, 7, 11, 547, 1291$ via a verified trial-division certificate (`isPrime_of_noDivisor`);
  2. Exact classification of all 64 divisors of $m = 815{,}634{,}435$ via Euclid's lemma;
  3. General theorem `perfectDeficiency_eq_sub_sum` reducing the greedy fold over `List.range (n + 1)` to $n - \sum_{d \mid n, d < n} d$ for any deficient number;
  4. `perfectDeficiency_815634435 : perfectDeficiency 815634435 = 6` and `disproves_a108864_odd_bound : ∃ m, m > 1155 ∧ m % 2 = 1 ∧ perfectDeficiency m ≤ 10`.
- **Python ([verify.py](verify.py)):** Independently verifies the factorization, primality, all 64 divisors, and exact greedy `perfectDeficiency(815634435) == 6`.
