#!/usr/bin/env python3
"""Deterministic verifier for OEIS A189286 (conjecture_3).

Verifies:
1. Exact values of a(0..4) against OEIS A189286.
2. v_2(t_k) == 2 * s_2(k) for all 0 <= k <= 128.
3. For all 1 <= n <= 128:
   - a(n) is an integer;
   - 8 divides a(n);
   - if n is a power of 2, v_2(S(n)) == 3 and v_2(a(n)) == 3 (so a(n)/8 is odd);
   - if n is not a power of 2, v_2(S(n)) >= 2*s_2(n) + 2 and v_2(a(n)) >= s_2(3n) + 2 >= 4 (so a(n)/8 is even).
"""

from __future__ import annotations

import math


def v2(x: int) -> int:
    assert x != 0
    return (abs(x) & -abs(x)).bit_length() - 1


def t_term(k: int) -> int:
    return math.comb(6 * k, 3 * k) * math.comb(3 * k, k)


def a(n: int) -> int:
    num = sum(t_term(k) * t_term(n - k) for k in range(n + 1))
    den = (2 * n - 1) * math.comb(3 * n, n)
    assert num % den == 0, f"a({n}) is not an integer!"
    return num // den


def main() -> int:
    expected = {0: -1, 1: 40, 2: 696, 3: 23408, 4: 969496}
    for n, val in expected.items():
        got = a(n)
        assert got == val, f"a({n}) = {got}, expected {val}"

    limit = 128
    t_vals = [t_term(k) for k in range(limit + 1)]
    for k, tk in enumerate(t_vals):
        assert v2(tk) == 2 * k.bit_count(), f"v2(t_{k}) mismatch"

    for n in range(1, limit + 1):
        s_val = sum(t_vals[k] * t_vals[n - k] for k in range(n + 1))
        an = a(n)
        assert an % 8 == 0, f"8 does not divide a({n})"
        is_pow2 = (n & (n - 1)) == 0
        if is_pow2:
            assert v2(s_val) == 3, f"Expected v2(S({n})) == 3, got {v2(s_val)}"
            assert v2(an) == 3, f"Expected v2(a({n})) == 3, got {v2(an)}"
            assert (an // 8) % 2 == 1
        else:
            s2_n = n.bit_count()
            s2_3n = (3 * n).bit_count()
            assert v2(s_val) >= 2 * s2_n + 2
            assert v2(an) >= s2_3n + 2 >= 4
            assert (an // 8) % 2 == 0

    print(f"[oeis-a189286] Verified a(0..4), v2(t_k), and 2-adic characterization for all 1 <= n <= {limit}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
