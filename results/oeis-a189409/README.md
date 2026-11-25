# OEIS A189409 (`conjecture_1`) — Counterexample: $(\mathrm{primorial}(9))^2 + 1$ Is Not Squarefree

- **Source:** J. M. Campbell (2011), [OEIS A189409](https://oeis.org/A189409); formalized as an open question in Google DeepMind's `formal-conjectures` (`FormalConjectures/OEIS/189409.lean`, `conjecture_1`).
- **Status:** Disproved (Complete resolution via explicit counterexample at $n = 9$).
- **Verification:** ✅ (Fully Lean 4 kernel-verified with zero `sorry` and zero extra axioms + reproducible Python verifier).

## Exact Statement

Let $\mathrm{primorial}(n) = \prod_{k=1}^{n} p_k$ be the $n$-th primorial, and define $a(n) = (\mathrm{primorial}(n))^2 + 1$.

**Question (`conjecture_1`):** Is $a(n)$ squarefree for every $n \ge 0$?

**Answer:** **No.**

## Counterexample ($n = 9$)

$$\mathrm{primorial}(9) = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23 = 223{,}092{,}870$$

$$a(9) = (\mathrm{primorial}(9))^2 + 1 = 49{,}770{,}428{,}644{,}836{,}901 = 29^2 \times 59{,}180{,}057{,}841{,}661$$

Since $29^2 = 841$ divides $a(9)$, $a(9)$ is **not** squarefree.

## Verification

- **Lean 4:** `lean/ConjectureLab/OeisA189409.lean` (`not_squarefree_a9`) proves $\neg\,\mathrm{IsSquarefree}(a(9))$ directly in the Lean 4 kernel via `rfl`.
- **Python:** `verify.py` verifies the exact factorization and confirms $n = 9$ is the smallest counterexample.
