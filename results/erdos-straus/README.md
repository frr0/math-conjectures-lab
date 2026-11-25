# Erdős–Straus Conjecture (1948) — Partial Theorem ($n \not\equiv 1 \pmod 8$)

- **Source:** P. Erdős (1948); open problem in elementary number theory.
- **Status:** Partial Result (the general conjecture remains open; here we formally prove 7 out of 8 residue classes modulo 8 and computationally verify all $2 \le n \le 100{,}000$).
- **Verification:** 🟡 (Partial Lean 4 theorem covering $87.5\%$ of all integers $n \ge 2$, zero `sorry`, zero extra axioms + Python verification up to $n = 100{,}000$).

## Exact Statement

For every integer $n \ge 2$, do there exist positive integers $x, y, z$ such that:

$$\frac{4}{n} = \frac{1}{x} + \frac{1}{y} + \frac{1}{z}$$

Equivalently, in positive natural numbers:

$$4xyz = n(yz + xz + xy)$$

## Proved Scope (Lean 4)

In `lean/ConjectureLab/ErdosStraus.lean`, we prove `erdos_straus_not_one_mod_eight`: for **every** $n \ge 2$ with $n \bmod 8 \ne 1$, positive integers $x, y, z$ exist via three explicit parametric identities:

1. **Even $n = 2k$ ($k \ge 1$):** $(x, y, z) = (k,\, 2k,\, 2k)$.
2. **$n \equiv 3 \pmod 4$ ($n = 4k + 3$, $m = k + 1$):** $(x, y, z) = (m,\, 2mn,\, 2mn)$.
3. **$n \equiv 5 \pmod 8$ ($n = 8k + 5$, $m = k + 1$):** $(x, y, z) = (2m,\, 2mn,\, mn)$.

## Computational Verification (Python)

`verify.py` independently verifies:
- the parametric formulas for all $2 \le n \le 100{,}000$ with $n \bmod 8 \ne 1$, and
- an explicit search finding valid $(x, y, z)$ for every remaining $n \equiv 1 \pmod 8$ with $n \le 100{,}000$.
