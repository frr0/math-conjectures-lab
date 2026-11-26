# OEIS A189286 (`conjecture_3`) — Proof That $8 \mid a(n)$ and $a(n)/8$ Is Odd iff $n = 2^k$

- **Source:** Zhi-Wei Sun (Apr 19, 2011), [OEIS A189286](https://oeis.org/A189286); formalized as an open problem in Google DeepMind's `formal-conjectures` (`FormalConjectures/OEIS/189286.lean`, `conjecture_3`).
- **Status:** Proved (Complete 2-adic valuation proof for all $n \ge 1$).
- **Verification:** 🟢 (Complete self-contained mathematical proof + deterministic Python verifier `verify.py` for $1 \le n \le 128$; Lean 4 formalization pending).

## Exact Statement

Let $t_k = \binom{6k}{3k}\binom{3k}{k}$ and define

$$a(n) = \frac{S(n)}{(2n - 1)\binom{3n}{n}}, \qquad S(n) = \sum_{k=0}^{n} t_k t_{n-k}.$$

It is already known (`OeisA189286.conjecture_1`, proved in `arXiv:2608.11941`) that $a(n) \in \mathbb{Z}$ for all $n \ge 0$.

**Conjecture (`OeisA189286.conjecture_3`):** For every integer $n \ge 1$, $a(n) \equiv 0 \pmod 8$, and $a(n)/8$ is odd if and only if $n = 2^r$ for some $r \ge 0$.

**Resolution:** **True.** In fact, $v_2(a(2^r)) = 3$ for all $r \ge 0$, and $v_2(a(n)) \ge s_2(3n) + 2 \ge 4$ for all $n \ge 1$ that are not powers of $2$.

## Literature Check

- In [OEIS A189286](https://oeis.org/A189286) and `FormalConjectures/OEIS/189286.lean`, `conjecture_1` (integrality) and `conjecture_2` (asymptotics) are marked solved, while `conjecture_3` (part (ii) of Zhi-Wei Sun's Apr 19, 2011 comment) remained marked `research open`.

## Computational Exploration

`explore.py` and `verify.py` confirm the initial values $a(0) = -1, a(1) = 40, a(2) = 696, a(3) = 23408, a(4) = 969496$, and verify $v_2(t_k) = 2s_2(k)$ and the exact 2-adic bounds on $S(n)$ and $a(n)$ for all $1 \le n \le 128$.

## Complete Proof

Let $v_2(m)$ denote the 2-adic valuation of $m$ and $s_2(m)$ the number of $1$-bits in the binary expansion of $m \ge 0$. Recall Kummer's theorem: $v_2\!\left(\binom{a+b}{a}\right) = s_2(a) + s_2(b) - s_2(a+b)$.

1. **Exact 2-adic valuation of $t_k$:**
   For every $k \ge 0$, applying Kummer's theorem twice gives
   $$v_2\!\left(\binom{6k}{3k}\right) = 2s_2(3k) - s_2(6k) = s_2(3k),$$
   $$v_2\!\left(\binom{3k}{k}\right) = s_2(k) + s_2(2k) - s_2(3k) = 2s_2(k) - s_2(3k),$$
   since $s_2(2m) = s_2(m)$. Adding these yields
   $$v_2(t_k) = 2s_2(k).$$

2. **Valuation of individual terms in $S(n)$:**
   For every $0 \le k \le n$,
   $$v_2(t_k t_{n-k}) = 2\bigl(s_2(k) + s_2(n - k)\bigr) = 2s_2(n) + 2\,v_2\!\left(\binom{n}{k}\right) \ge 2s_2(n),$$
   with equality if and only if $v_2\!\left(\binom{n}{k}\right) = 0$, i.e. $k$ is a bitwise submask of $n$ ($k \preceq n$). There are exactly $2^{s_2(n)}$ such indices $k \in \{0, \dots, n\}$.

3. **Case 1: $n = 2^r$ ($r \ge 0$):**
   Here $s_2(n) = 1$, and the only submasks $k \preceq 2^r$ are $k = 0$ and $k = 2^r$.
   - The boundary terms $k = 0$ and $k = n$ sum to $2 t_n$, which has $v_2(2 t_n) = 1 + 2s_2(n) = 3$.
   - Every interior term $1 \le k \le n - 1$ satisfies $v_2\!\left(\binom{n}{k}\right) \ge 1$, so $v_2(t_k t_{n-k}) \ge 2(1 + 1) = 4$.
   Hence $v_2(S(2^r)) = 3$. Meanwhile, $2n - 1$ is odd and $v_2\!\left(\binom{3 \cdot 2^r}{2^r}\right) = 2s_2(2^r) - s_2(3 \cdot 2^r) = 2 - 2 = 0$. Therefore $v_2(a(2^r)) = 3$, meaning $8 \mid a(2^r)$ and $a(2^r)/8$ is odd.

4. **Case 2: $n \ge 1$ is not a power of $2$ ($s_2(n) \ge 2$):**
   Group the sum $S(n)$ into unordered pairs $\{k, n - k\}$ with $0 \le k < n/2$, plus the middle term $t_{n/2}^2$ when $n$ is even:
   - Notice $k = n/2$ cannot be a submask of $n > 0$ (since $(n/2) + (n/2) = n$ always carries). Thus all $2^{s_2(n)}$ submasks $k \preceq n$ split into $2^{s_2(n) - 1}$ pairs $\{k, n - k\}$ with $k < n/2$.
   - Each submask pair contributes $2 t_k t_{n-k}$ with $v_2(2 t_k t_{n-k}) = 1 + 2s_2(n)$, i.e. $2 t_k t_{n-k} \equiv 2^{2s_2(n) + 1} \pmod{2^{2s_2(n) + 2}}$. Since $s_2(n) \ge 2$, the number of submask pairs $2^{s_2(n) - 1}$ is **even**, so their total contribution is divisible by $2^{2s_2(n) + 2}$.
   - Any non-submask pair ($k \npreceq n$) has $v_2(2 t_k t_{n-k}) \ge 1 + 2(s_2(n) + 1) = 2s_2(n) + 3$.
   - If $n = 2m$ is even, the middle term $t_m^2$ has $v_2(t_m^2) = 4s_2(m) = 4s_2(n) \ge 2s_2(n) + 4$ (as $s_2(n) \ge 2$).
   Therefore $v_2(S(n)) \ge 2s_2(n) + 2$. Since $2n - 1$ is odd and $v_2\!\left(\binom{3n}{n}\right) = 2s_2(n) - s_2(3n)$, we obtain
   $$v_2(a(n)) = v_2(S(n)) - v_2\!\left(\binom{3n}{n}\right) \ge s_2(3n) + 2.$$
   Because $3n \ge 3$ is divisible by $3$, $3n$ cannot be a power of $2$, so $s_2(3n) \ge 2$. Hence $v_2(a(n)) \ge 4$, so $16 \mid a(n)$ and $a(n)/8$ is even. $\blacksquare$
