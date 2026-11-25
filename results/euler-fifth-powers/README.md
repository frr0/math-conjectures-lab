# Euler's Sum of Powers Conjecture ($k = 5$) — Pipeline Calibration

- **Source:** L. Euler (1769); disproved by L. J. Lander & T. R. Parkin, *Counterexample to Euler's conjecture on sums of like powers*, Bull. Amer. Math. Soc. 72 (1966), 1079.
- **Status:** Disproved (Historical Counterexample — used to calibrate this repository's Python + Lean 4 + CI pipeline)
- **Verification:** ✅ (Lean 4 kernel-verified + Python reproducible verifier)

## Exact Statement

Euler conjectured in 1769 that for every integer $k \ge 3$, at least $k$ positive $k$-th powers are required to sum to a $k$-th power. For $k = 5$, this claims there exist no positive integers $a, b, c, d, e$ such that:

$$a^5 + b^5 + c^5 + d^5 = e^5$$

## Counterexample

$$27^5 + 84^5 + 110^5 + 133^5 = 144^5 = 61{,}917{,}364{,}224$$

## Verification

- **Python:** Run `python3 verify.py` (checks the arithmetic identity and also rediscovers the minimal counterexample via a fast meet-in-the-middle search).
- **Lean 4:** Formally proved in `lean/ConjectureLab/EulerFifthPowers.lean` (`euler_fifth_powers_counterexample`) with zero `sorry` and zero extra axioms.
