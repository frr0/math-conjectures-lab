# OEIS A046969 (`conjecture1`) — Proof That $a(p)/12 = 2p - 1$ Is Prime

- **Source:** Lorenzo Sauras Altuzarra (Oct 13, 2020), [OEIS A046969](https://oeis.org/A046969); formalized as an open problem in Google DeepMind's `formal-conjectures` (`FormalConjectures/OEIS/46969.lean`, `conjecture1`).
- **Status:** Proved (Complete mathematical resolution for all primes $p > 3$ with $2p - 1$ prime).
- **Verification:** 🟢 (Complete self-contained mathematical proof + exact Python verifier `verify.py` checking $p \le 100$; Lean 4 formalization pending local toolchain).

## Exact Statement

Let $B_m$ denote the $m$-th Bernoulli number ($B_0 = 1$, $B_1 = -1/2$, $B_2 = 1/6$, $\dots$), and for $n \ge 1$ define

$$a(n) = \mathrm{den}\!\left(\frac{B_{2n}}{2n(2n - 1)}\right),$$

the reduced denominator of the rational number $\frac{B_{2n}}{2n(2n-1)}$.

**Conjecture I (`OeisA46969.conjecture1`):** For every prime $p > 3$ such that $2p - 1$ is also prime (i.e., $p \in \mathrm{A005382}(n)$ for $n > 2$), the quotient $a(p)/12$ is prime.

**Resolution:** **True.** In fact, $a(p) = 12(2p - 1)$, so $a(p)/12 = 2p - 1$ for every such prime $p$.

## Literature Check

- In [OEIS A046969](https://oeis.org/A046969), Lorenzo Sauras Altuzarra (Oct 13, 2020) stated Conjecture I and Conjecture II. Conjecture II was disproved at $n = 236791$ (recorded in `FormalConjectures/OEIS/46969.lean`), while Conjecture I remained marked `research open`.

## Computational Exploration

Running `explore.py` and `verify.py` confirms the exact values $a(1)=12, a(2)=360, a(3)=1260, a(4)=1680, a(5)=1188$ and verifies for all primes $3 < p \le 100$ with $q = 2p - 1$ prime ($p \in \{7, 19, 31, 37, 79, 97\}$) that $\mathrm{den}(B_{2p}) = 6$, $p \mid \mathrm{num}(B_{2p})$, $q \nmid \mathrm{num}(B_{2p})$, and $a(p) = 12q$.

## Complete Proof

Let $p > 3$ be a prime such that $q = 2p - 1$ is also prime.

1. **Modular constraints ($p \equiv 1 \pmod 6$ and $2p + 1$ composite):**
   Since $p > 3$ is prime, $p$ is odd and $p \not\equiv 0 \pmod 3$. If $p \equiv 2 \pmod 3$, then $2p - 1 \equiv 3 \equiv 0 \pmod 3$ while $2p - 1 \ge 9 > 3$, contradicting the primality of $2p - 1$. Therefore $p \equiv 1 \pmod 3$, so $p \equiv 1 \pmod 6$ (in particular $p \ge 7$ and $q = 2p - 1 \ge 13$). Moreover, $2p + 1 \equiv 3 \equiv 0 \pmod 3$ and $2p + 1 \ge 15 > 3$, so $2p + 1$ is composite.

2. **Denominator of $B_{2p}$ via the Von Staudt–Clausen Theorem:**
   By the Von Staudt–Clausen theorem,
   $$\mathrm{den}(B_{2p}) = \prod_{\substack{r \text{ prime} \\ (r - 1) \mid 2p}} r.$$
   Since $p$ is an odd prime, the positive divisors of $2p$ are $1, 2, p, 2p$, so $(r - 1) \mid 2p$ forces $r \in \{2, 3, p + 1, 2p + 1\}$. Both $2$ and $3$ are prime, $p + 1 > 2$ is even (composite), and $2p + 1$ is composite by Step 1. Hence
   $$\mathrm{den}(B_{2p}) = 2 \cdot 3 = 6.$$
   Write $B_{2p} = N / 6$ with $N \in \mathbb{Z}$ and $\gcd(N, 6) = 1$.

3. **Divisibility $p \mid N$ via Kummer's Congruence:**
   Write $2p = (p + 1) + (p - 1)$. Since $p \ge 7$ is odd, $p + 1$ is even and $(p - 1) \nmid (p + 1)$ (as $p - 1 \ge 6 > 2$). By Kummer's congruence modulo $p$,
   $$\frac{B_{2p}}{2p} \equiv \frac{B_{p+1}}{p+1} \pmod p.$$
   By Von Staudt–Clausen, $p \nmid \mathrm{den}(B_{p+1})$ because $(p - 1) \nmid (p + 1)$, and clearly $p \nmid (p + 1)$. Hence $\frac{B_{p+1}}{p+1}$ is a $p$-adic integer, so $\frac{B_{2p}}{2p} = \frac{N}{12p}$ is a $p$-adic integer. Since $\gcd(p, 12) = 1$, it follows that $p \mid N$.

4. **Non-divisibility $q \nmid N$ via Kummer's Congruence:**
   With $q = 2p - 1 \ge 13$ prime, write $2p = 2 + (q - 1)$. Since $q - 1 \ge 12 > 2$, $(q - 1) \nmid 2$, so Kummer's congruence modulo $q$ gives
   $$\frac{B_{2p}}{2p} \equiv \frac{B_2}{2} = \frac{1}{12} \pmod q.$$
   Because $q \ge 13$, we have $q \nmid 12$ and $q \nmid 2p$ (since $2p = q + 1$). Therefore $B_{2p} \equiv \frac{2p}{12} \not\equiv 0 \pmod q$, which means $q \nmid N$.

5. **Exact value of $a(p)$:**
   Let $M = N / p \in \mathbb{Z}$ (by Step 3). Then
   $$\frac{B_{2p}}{2p(2p - 1)} = \frac{N / 6}{2pq} = \frac{M}{12q}.$$
   From $\gcd(N, 6) = 1$ we have $\gcd(M, 6) = 1$, hence $\gcd(M, 12) = 1$. From $q \nmid N$ we have $q \nmid M$, and since $q$ is prime, $\gcd(M, q) = 1$. Thus $\gcd(M, 12q) = 1$, so the reduced denominator is
   $$a(p) = 12q = 12(2p - 1).$$
   Consequently $a(p) / 12 = 2p - 1$, which is prime by hypothesis. $\blacksquare$
