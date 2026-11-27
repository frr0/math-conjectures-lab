# OEIS A001481 (J. Lowell, 2022): Proof that no two distinct sums of two squares add to a power of 2 except 0 + 2^k

- **Source:** J. Lowell, comment of Jan 14 2022 in [OEIS A001481](https://oeis.org/A001481). The problem is listed as open on [lefttosolve.com](https://lefttosolve.com/p/oeis-a001481) ("OEIS conjectures (not formalized)").
- **Status:** Proved (full resolution).
- **Verification:** ✅ Lean 4 module `lean/ConjectureLab/OeisA001481.lean`, theorem `lowell_conjecture`. There is also a finite check, `verify.py` ($k \le 20$).

## Exact Statement

A001481 lists the numbers $n \ge 0$ with $n = x^2 + y^2$ for some $x, y \in \mathbb{N}$. The OEIS comment reads:

> Conjecture: barring the 0+2, 0+4, 0+8, 0+16, ... sequence, the sum of 2 distinct terms in this sequence is never a power of 2.

**Theorem.** Let $a \ne b$ be terms of A001481 and $k \ge 0$ with $a + b = 2^k$. Then $\{a, b\} = \{0, 2^k\}$. Conversely, every $2^k$ is a term of A001481.

The case $k = 0$ gives $0 + 1$. This is the same family $0 + 2^k$, even though the comment's list starts at $0 + 2$.

## Literature Check

- The OEIS entry still calls the statement a "Conjecture". It gives no proof and no reference to one.
- It is not formalized in google-deepmind/formal-conjectures. lefttosolve.com marks it "Open".
- The argument below is elementary. Someone may have noticed it before, but we found no record of that.

## Proof

1. **Odd terms are $1 \bmod 4$.** Every square is $0$ or $1 \bmod 4$. So an odd $x^2 + y^2$ is $1 \bmod 4$.
2. **Halving.** Suppose $2m = x^2 + y^2$. Then $x \equiv y \pmod 2$. Assume $x = y + 2t$. Then $m = (y + t)^2 + t^2$, so $m$ is in A001481.
3. **Descent on $k$.** Let $a \ne b$ be terms of A001481 with $a + b = 2^k$.
   - If $k = 0$, then $a + b = 1$, so one of the two is $0$.
   - Suppose $k \ge 1$, so $a + b$ is even.
   - **$a$ and $b$ have opposite parity.** Then $a + b$ is odd. This is impossible.
   - **Both are odd.** By step 1, $a + b \equiv 2 \pmod 4$, so $2^k = 2$. Then $a = b = 1$, which contradicts $a \ne b$.
   - **Both are even.** Write $a = 2a'$ and $b = 2b'$. By step 2, $a'$ and $b'$ are in A001481. They are distinct and $a' + b' = 2^{k-1}$. By induction, one of them is $0$.
   - In every case one of $a, b$ is $0$, so the other is $2^k$.
4. **The exceptions are genuine.** $2^{2j} = (2^j)^2 + 0^2$ and $2^{2j+1} = (2^j)^2 + (2^j)^2$.

## Adversarial Review

- **Quantifiers.** The theorem covers all $k \ge 0$ and all $a, b \in \mathbb{N}$. Ordered pairs are covered by symmetry: the Lean statement concludes $(a,b) = (0,2^k)$ or $(a,b) = (2^k,0)$.
- **Distinctness is needed.** Without it, $2^{k-1} + 2^{k-1} = 2^k$, and $2^{k-1}$ is a term.
- **No hidden assumptions.** $0$ is a term ($0 = 0^2 + 0^2$), matching the OEIS sequence, which starts $0, 1, 2, 4, \dots$
- **No spec gaming.** The Lean statement matches the theorem above exactly. It uses `IsSumTwoSq n := ∃ x y : ℕ, n = x^2 + y^2`.

## Files

- `explore.py`: brute-force search for $k \le 24$ (no exceptions found). It also checks that odd terms are $1 \bmod 4$.
- `verify.py`: deterministic finite check for $k \le 20$.
