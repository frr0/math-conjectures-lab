# OEIS A092243 — Prime-Gap Tug-of-War (`conjecture1`)

## Conjecture Statement
Let $p_0 = 2, p_1 = 3, p_2 = 5, \dots$ be the 0-indexed sequence of prime numbers, and let $g_k = p_k - p_{k-1}$ be the $k$-th prime gap ($k \ge 1$). Define the "tug-of-war" score between prime-gap increases and decreases:

$$a(n) = \sum_{k=2}^{n} \operatorname{sign}(g_k - g_{k-1}) \quad (n \ge 2), \qquad a(0) = a(1) = 0.$$

In `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/92243.lean`), `conjecture1` asks:

> **Question (`OeisA92243.conjecture1`):** Is $a(n) > 0$ for some $n > 250{,}000$?

## Outcome
**Resolved affirmatively (🟢 Computer-assisted + Lean 4 verified structural theorem).**

The **smallest** index $n > 250{,}000$ with $a(n) > 0$ is **$n = 261{,}150$**:
- $p_{261148} = 3{,}666{,}529$, $p_{261149} = 3{,}666{,}539$, $p_{261150} = 3{,}666{,}581$.
- $g_{261149} = 10$, $g_{261150} = 42 > 10$.
- $a(261{,}149) = 0$, and therefore $a(261{,}150) = 0 + \operatorname{sign}(42 - 10) = 1 > 0$.

Further computation up to $p_{283145} = 3{,}999{,}971$ shows $14{,}902$ indices $n \in (250{,}000, 283{,}145]$ with $a(n) > 0$, reaching a maximum score of $a(273{,}677) = 83$.

## Literature Check
- Source: [OEIS A092243](https://oeis.org/A092243) and `google-deepmind/formal-conjectures` (`FormalConjectures/OEIS/92243.lean`), where `conjecture1` is listed as `research open, question`.
- The remaining questions in `92243.lean` (`conjecture2`–`conjecture5`: boundedness and infinitude of positive/negative terms) remain open.

## Verification
- **Python (`verify.py`):** Exact Sieve of Eratosthenes up to $4{,}000{,}000$, verifying $a(0..5)$ against the OEIS/Lean test values, confirming $a(n) \le 0$ for all $250{,}000 < n \le 261{,}149$, and certifying $a(261{,}150) = 1 > 0$ (and $a(273{,}677) = 83$).
- **Lean 4 ([OeisA092243.lean](../../lean/ConjectureLab/OeisA092243.lean)):** Pure Lean 4 formalization of `tugOfWarScore`, exact base-case verification (`a 0` through `a 5`), general append/step recurrence `tugOfWarScore_append_step`, positivity lemma `score_pos_of_zero_and_increase`, and the exact step transition at $n = 261{,}150$ (`witness_261150_step`).
