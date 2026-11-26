# OEIS A238281 (`conjecture_2`) — Disproof: Equal Prime Counts in Adjacent Intervals

- **Source:** Zhi-Wei Sun (2014), [OEIS A238281](https://oeis.org/A238281); formalized in Google DeepMind's `formal-conjectures` (`FormalConjectures/OEIS/238281.lean`, `conjecture_2`).
- **Status:** Disproved (Explicit counterexamples at $n = 14$ and $n = 286$).
- **Verification:** 🟢 (Deterministic Python verifier `verify.py` + Lean 4 module `lean/ConjectureLab/OeisA238281.lean`).

## Exact Statement

**Conjecture (`conjecture_2`):** For every integer $n > 1$ with $n \ne 8$, there exists a positive integer $k < n$ such that $2k + 1$ is prime and the two adjacent half-open intervals $((k-1)n, kn]$ and $(kn, (k+1)n]$ contain the same number of primes:

$$\pi(kn) - \pi((k-1)n) = \pi((k+1)n) - \pi(kn).$$

## Literature Check

- In [OEIS A238281](https://oeis.org/A238281), Zhi-Wei Sun (Feb 2014) conjectured this property.
- The statement was catalogued as `conjecture_2` in Google DeepMind's `formal-conjectures` benchmark (`FormalConjectures/OEIS/238281.lean`).

## Disproof & Explicit Counterexample ($n = 14$)

For $n = 14$, any valid multiplier $k$ must satisfy $1 \le k < 14$ and $2k + 1 \in \mathbb{P}$. The only candidates are:

$$k \in \{1, 2, 3, 5, 6, 8, 9, 11\}$$

Evaluating the number of primes in the adjacent intervals $((k-1)\cdot 14, k\cdot 14]$ and $(k\cdot 14, (k+1)\cdot 14]$ gives:

| $k$ | $2k+1$ | Interval 1 $((k-1)\cdot 14, k\cdot 14]$ | Primes in 1 | Interval 2 $(k\cdot 14, (k+1)\cdot 14]$ | Primes in 2 | Equal? |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 1 | 3 | $(0, 14]$ | 6 | $(14, 28]$ | 3 | ❌ ($6 \ne 3$) |
| 2 | 5 | $(14, 28]$ | 3 | $(28, 42]$ | 4 | ❌ ($3 \ne 4$) |
| 3 | 7 | $(28, 42]$ | 4 | $(42, 56]$ | 3 | ❌ ($4 \ne 3$) |
| 5 | 11 | $(56, 70]$ | 3 | $(70, 84]$ | 4 | ❌ ($3 \ne 4$) |
| 6 | 13 | $(70, 84]$ | 4 | $(84, 98]$ | 2 | ❌ ($4 \ne 2$) |
| 8 | 17 | $(98, 112]$ | 4 | $(112, 126]$ | 1 | ❌ ($4 \ne 1$) |
| 9 | 19 | $(112, 126]$ | 1 | $(126, 140]$ | 4 | ❌ ($1 \ne 4$) |
| 11 | 23 | $(140, 154]$ | 2 | $(154, 168]$ | 3 | ❌ ($2 \ne 3$) |

For all eight admissible $k$, the prime counts differ. Hence no such $k$ exists for $n = 14$, disproving the conjecture.
(The next counterexample occurs at $n = 286$).

## Verification

- `verify.py`: Independently verifies primality and counts for all candidates at $n = 14$ and $n = 286$.
- `lean/ConjectureLab/OeisA238281.lean`: Formalizes the interval prime counting functions and the structural counterexample theorem.
