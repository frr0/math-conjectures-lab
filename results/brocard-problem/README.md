# Brocard's Problem (1876) — Brown Numbers & Last-Digit Obstruction

- **Source:** H. Brocard (1876, 1885); S. Ramanujan (1913). Open problem in number theory.
- **Status:** Partial Result (the general conjecture that only $n \in \{4, 5, 7\}$ exist remains open; here we formally verify all 3 known Brown pairs and prove the universal last-digit constraint $m \equiv \pm 1 \pmod{10}$ for all $n \ge 5$, plus computationally screen $1 \le n \le 1{,}000$).
- **Verification:** 🟡 (Partial Lean 4 theorems with zero `sorry` and zero extra axioms + exact Python verifier up to $n = 1{,}000$).

## Exact Statement

Find all pairs of positive integers $(n, m)$ (called *Brown numbers*) such that:

$$n! + 1 = m^2$$

It is conjectured that the only solutions are $(4, 5)$, $(5, 11)$, and $(7, 71)$.

## Proved Scope (Lean 4)

In `lean/ConjectureLab/BrocardProblem.lean`, we prove:
1. `brocard_known_solutions`: $(4, 5)$, $(5, 11)$, and $(7, 71)$ satisfy $n! + 1 = m^2$.
2. `ten_dvd_fact`: for every $n \ge 5$, $10 \mid n!$.
3. `brocard_last_digit`: for **every** $n \ge 5$ and every $m \in \mathbb{N}$ with $n! + 1 = m^2$, necessarily $m \bmod 10 = 1$ or $m \bmod 10 = 9$.

## Computational Verification (Python)

`verify.py` uses exact integer square roots (`math.isqrt`) to verify all $1 \le n \le 1{,}000$, confirming that the only solutions in this range are $n \in \{4, 5, 7\}$.
