# OEIS A100475 — No Positive Starting Value Ever Enters a Loop

- **Source:** J. Vos Post (2004), [OEIS A100475](https://oeis.org/A100475); formalized as an open question in Google DeepMind's `formal-conjectures` (`FormalConjectures/OEIS/100475.lean`).
- **Status:** Disproved (Complete resolution: the answer to *"does any positive start other than 1 enter a loop?"* is **No** — in fact, *no* positive starting value $x \ge 1$ is ever ultimately periodic).
- **Attribution / Literature Note:** Independently rediscovered here; a literature check confirmed that an independent formal resolution using the same prime-counting + finite-escape method was also recorded on `palomar-registry.org`.
- **Verification:** 🟢 (Lean 4 formalizes the escape & digit-reversal theorems with zero `sorry` and zero custom axioms; Python verifies the finite certificate for all $1 \le k \le 22{,}027$ bridging to Rosser's theorem $p_k > k \ln k$).

## Exact Statement

Define $f(k) = \mathrm{reverseDigits}_{10}(p_k)$ for $k \ge 1$, where $p_k$ is the $k$-th prime ($p_1 = 2, p_2 = 3, \dots$), and consider the orbit $a(0) = x$, $a(n+1) = f(a(n))$.

**Question:** Does there exist $x \ge 1$ ($x \ne 1$) such that the orbit starting at $x$ is ultimately periodic?

**Answer:** **No.** For *every* $x \ge 1$, the orbit escapes to $+\infty$ and is never ultimately periodic.

## Complete Proof

1. **Strict growth for $p_k \ge 10k$:** Suppose $p_k \ge 10k$ and $p_k$ has $D \ge 2$ decimal digits, so $10^{D-1} \le p_k < 10^D$. Since $p_k \ge 10$ is prime, $p_k \bmod 10 \in \{1, 3, 7, 9\}$ (its last digit is nonzero). Hence $\mathrm{reverseDigits}_{10}(p_k)$ also has $D$ digits, giving:
   $$f(k) = \mathrm{reverseDigits}_{10}(p_k) \ge 10^{D-1} > \frac{p_k}{10} \ge k.$$
   Thus $f(k) > k$ whenever $p_k \ge 10k$. (Formalized in `step_gt_of_ten_mul`.)
2. **Threshold via Rosser's Theorem:** By Rosser's theorem (1939), $p_k > k \ln k$ for all $k \ge 1$. For all $k \ge 22{,}027 > e^{10}$, $\ln k > 10$, hence $p_k > 10k$. Direct computation in `verify.py` confirms $p_k \ge 10k$ for all $6{,}473 \le k \le 22{,}027$ as well (the largest exception is $k = 6{,}472$, where $p_{6472} = 64{,}717 < 64{,}720$). Therefore $f(k) > k$ for **every** $k \ge 6{,}473$.
3. **Finite Escape:** Direct computation in `verify.py` verifies that for **every** $1 \le x \le 6{,}472$, the orbit reaches a value $\ge 6{,}473$ in at most $9$ steps.
4. **No Periodicity:** Once an orbit enters $[K, \infty)$ where $f(k) > k$, it is strictly increasing forever and therefore cannot be ultimately periodic. (Formalized in `not_periodic_of_escape`.)
