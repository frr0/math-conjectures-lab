# OEIS A001227 (Omar E. Pol, 2017): Proof that A001227 = A067742 + 2·A131576 = A082647 + A131576

- **Source:** Omar E. Pol, comment of Feb 15 2017 in [OEIS A001227](https://oeis.org/A001227). The same identities appear as conjectures in [A067742](https://oeis.org/A067742), [A131576](https://oeis.org/A131576) and [A082647](https://oeis.org/A082647). The problem is listed as open on [lefttosolve.com](https://lefttosolve.com/p/oeis-a001227) ("OEIS conjectures (not formalized)").
- **Status:** Proved (full resolution). Literature note:
  - The second identity is classical. N. J. A. Sloane remarks in A131576 (Dec 2020) that it "follows immediately from the definitions".
  - The first identity follows from the second together with Theorem 2 in A067742 (Chapman et al. 2001; Hirschhorn & Hirschhorn 2005).
  - The A001227 comment is still labeled "Conjectures", and lefttosolve still lists the problem as open. What this entry adds is a self-contained elementary proof and a full Lean formalization.
- **Verification:** ✅
  - The Lean 4 module `lean/ConjectureLab/OeisA001227.lean` (`pol_conjecture`) proves both identities for every $n$.
  - All four sequences are defined in Lean exactly as their OEIS names state. The middle-divisor condition uses `Real.sqrt`.
  - `verify.py` checks both identities from brute-force definitions for $n \le 3000$.

## Exact Statement

- **A001227**$(n)$: number of odd divisors of $n$.
- **A067742**$(n)$: number of divisors $d$ of $n$ with $\sqrt{n/2} \le d < \sqrt{2n}$ ("middle divisors").
- **A131576**$(n)$: number of ways to write $n$ as a sum of an even number of consecutive positive integers.
- **A082647**$(n)$: number of ways to write $n$ as a sum of $d$ consecutive positive integers, where $d$ is a divisor of $n$.

**Theorem.** For every $n \ge 1$: $A001227(n) = A067742(n) + 2\,A131576(n) = A082647(n) + A131576(n)$.

## Proof

Fix $n \ge 1$. Write $\mathcal A = \{d \mid n : d \text{ odd},\ d^2 < 2n\}$ and $\mathcal B = \{d \mid n : d \text{ odd},\ d^2 > 2n\}$. An odd $d$ never satisfies $d^2 = 2n$, so $A001227(n) = |\mathcal A| + |\mathcal B|$.

1. **Runs.** $n = m + (m+1) + \dots + (m+k-1)$ with $m, k \ge 1$ iff $2n = k\,j$ with $j = 2m+k-1$. The two factors $j$ and $k$ have opposite parity, and $j > k$.
2. **A082647 $= |\mathcal A|$.**
   - In a run, $k \mid n$ iff $k$ is odd. If $k$ is odd, then $k \mid 2n$ gives $k \mid n$. If $k = 2r$ and $n = kq$, then $2q = j$, but $j$ is odd.
   - The map $(m,k) \mapsto k$ sends the runs with $k \mid n$ bijectively onto $\mathcal A$. Here $k^2 < kj = 2n$. The inverse is $d \mapsto \big((2n/d + 1 - d)/2,\ d\big)$.
3. **A131576 $= |\mathcal B|$.** The map $(m,k) \mapsto j$ sends the even-length runs bijectively onto $\mathcal B$:
   - $j$ is odd, $j \mid n$ (since $n = (k/2)\,j$), and $j^2 > jk = 2n$;
   - the inverse is $d \mapsto \big((d + 1 - 2n/d)/2,\ 2n/d\big)$.
4. **A067742 $= |\mathcal A| - |\mathcal B|$.** Let $S = \{d \mid n : d^2 < 2n\}$ and $U = \{d \mid n : 2d^2 < n\} \subseteq S$. The middle divisors are exactly $S \setminus U$, so $A067742 = |S| - |U|$. Then:
   - $S$ splits into its odd part, which is $\mathcal A$, and its even part $S_{\rm even}$;
   - $U$ splits into $U_1 = \{d \in U : 2d \mid n\}$ and $U_2 = \{d \in U : 2d \nmid n\}$;
   - $d \mapsto 2d$ is a bijection $U_1 \to S_{\rm even}$, because $(2d)^2 < 2n \iff 2d^2 < n$;
   - $d \mapsto n/d$ is a bijection $U_2 \to \mathcal B$: $2d \nmid n$ means $n/d$ is odd, and $(n/d)^2 > 2n \iff 2d^2 < n$.
   
   Hence $A067742 = |S_{\rm even}| + |\mathcal A| - |S_{\rm even}| - |\mathcal B| = |\mathcal A| - |\mathcal B|$.
5. **Conclusion.**
   - $A067742 + 2\,A131576 = (|\mathcal A| - |\mathcal B|) + 2|\mathcal B| = |\mathcal A| + |\mathcal B| = A001227$.
   - $A082647 + A131576 = |\mathcal A| + |\mathcal B| = A001227$.

## Adversarial Review

- **Offset.** The OEIS sequences start at $n = 1$. The Lean theorem holds for every $n \in \mathbb N$. At $n = 0$ all four counts are $0$, so the identity holds trivially.
- **"Consecutive positive integers".** A131576 says "consecutive integers". Its data ($a(1)=0$, $a(3)=1$) only matches positive integers: allowing $0$ or negative integers would give $3 = (-2)+\dots+3$ and more. `explore.py` checks our definitions against the first 30 OEIS terms of all four sequences.
- **A082647 with several $d$.** For a fixed length $d$ there is at most one run, so counting pairs (start, length) equals counting the admissible $d$.
- **Middle divisors.** Lean states the condition with real square roots, exactly as in the OEIS name. `middle_iff` proves it equivalent to $n \le 2d^2 < 4n$.
- **No bounded search in the definitions.** `runs n` filters the box $[1,n]^2$. `mem_runs` proves that this box loses no representation.

## Files

- `defs.py`: brute-force definitions of the four sequences.
- `explore.py`: comparison with OEIS data, plus a table of $|\mathcal A|$, $|\mathcal B|$ and the middle-divisor count for $n \le 40$.
- `verify.py`: deterministic check of both identities for $1 \le n \le 3000$.
