# OEIS A004215 (Tilman Neumann, 2020): Proof that #terms < 2^n = A023105(n) − 2

- **Source:** Tilman Neumann, comment of Sep 20 2020 in [OEIS A004215](https://oeis.org/A004215). The same comment appears in [A023105](https://oeis.org/A023105). The problem is listed as open on [lefttosolve.com](https://lefttosolve.com/p/oeis-a004215) ("OEIS conjectures (not formalized)"). It is not in google-deepmind/formal-conjectures.
- **Status:** Proved (full resolution, written proof).
- **Verification:** 🟢
  - Lean 4 module `lean/ConjectureLab/OeisA004215.lean` (`neumann_count`) proves the counting core: $\#\{n < 2^m : n = 4^a(8b+7)\} + 2 = \lfloor (2^m+10)/6 \rfloor$ for all $m \ge 1$.
  - Two classical inputs are proved in writing below or cited, but not formalized: Legendre's three-square theorem, and the residue count of A023105.
  - `verify.py` checks the original statement directly from the definitions for $m \le 16$.

## Exact Statement

- A004215 is the set of positive integers that are a sum of 4 but no fewer nonzero squares.
- $A023105(n)$ is the number of distinct quadratic residues mod $2^n$, that is, $\#\{x^2 \bmod 2^n\}$.

**Theorem.** For every $n \ge 1$: $\#\{t \in A004215 : t < 2^n\} = A023105(n) - 2$.

The statement is false at $n = 0$, where it would give $0 = 1 - 2$. The OEIS comment on A023105 restricts it to $n > 0$.

## Proof

Write $C(m) = \#\{t \in A004215 : t < 2^m\}$ and $Q(m) = A023105(m)$.

1. **Legendre's form.**
   - Lagrange's theorem says every positive integer is a sum of 4 squares.
   - Legendre's three-square theorem (Legendre 1798, Gauss 1801) says $t$ is a sum of 3 squares, zeros allowed, iff $t \ne 4^a(8b+7)$.
   - A sum of at most 3 nonzero squares is the same thing as a sum of 3 squares with zeros allowed.
   - So A004215 $= \{4^a(8b+7)\}$.
2. **Recurrence for $C$.**
   - $t = 4^a(8b+7)$ holds iff either $t \equiv 7 \pmod 8$, or $4 \mid t$ and $t/4$ has the same form.
   - So the terms below $2^{m+3}$ are of two disjoint kinds:
     - $8b+7$ with $b < 2^m$, which gives $2^m$ terms;
     - $4s$ with $s$ a term below $2^{m+1}$.
   - Hence $C(m+3) = 2^m + C(m+1)$.
   - Every term is $\ge 7$, so $C(0) = C(1) = C(2) = 0$.
3. **Recurrence for $Q$.** Take $m \ge 3$.
   - **Odd residues.** For odd $x$, $x^2 \equiv 1 \pmod 8$. For $m \ge 3$, the equation $x^2 \equiv y^2 \pmod{2^m}$ with $x, y$ odd holds iff $x \equiv \pm y \pmod{2^{m-1}}$. So squaring is 4-to-1 on the $2^{m-1}$ odd residues. That gives exactly $2^{m-3}$ odd squares, so every class $\equiv 1 \pmod 8$ is a square.
   - **Even residues.** For even $x = 2y$, $x^2 \bmod 2^m$ is $4\,(y^2 \bmod 2^{m-2})$. So the even squares mod $2^m$ are in bijection with the squares mod $2^{m-2}$.
   - Hence $Q(m) = 2^{m-3} + Q(m-2)$, that is, $Q(m+3) = 2^m + Q(m+1)$.
   - The initial values are $Q(1) = 2$ ($\{0,1\}$) and $Q(2) = 2$ ($\{0,1\}$).
4. **Conclusion.** $C + 2$ and $Q$ satisfy the same recurrence $X(m+3) = 2^m + X(m+1)$. They agree at $m = 1$ and $m = 2$. Hence $C(m) = Q(m) - 2$ for all $m \ge 1$.
5. **Closed form.** Lean proves the same result in closed form: $C(m) + 2 = \lfloor (2^m+10)/6 \rfloor$. This is the known formula for A023105.

## Adversarial Review

- **Boundary $n = 0$.** It is excluded, matching the comment ("for n>0").
- **"Terms < $2^n$".** Strict inequality, consistent in all three places: the proof, `verify.py` and Lean.
- **"Nonzero squares".** Handled in step 1. 0 is not a term, so the count starts at $t \ge 1$.
- **Dependence on Legendre's theorem.** Step 1 relies on it. `verify.py` avoids it: for $m \le 16$ it computes the minimal number of nonzero squares directly by brute force.
- **Lean scope.** Lean formalizes the counting core only, so the label is 🟢, not ✅. No weakened hypothesis is presented as the full theorem.

## Files

- `explore.py`: tables of $C(m)$ and $Q(m)$ for $m \le 20$, plus a check of the shared recurrence.
- `verify.py`: deterministic check of the original statement for $1 \le m \le 16$.
