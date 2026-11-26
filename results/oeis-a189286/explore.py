#!/usr/bin/env python3
"""Computational exploration of OEIS A189286 (conjecture_3).

a(n) = (sum_{k=0}^n t_k * t_{n-k}) / ((2n - 1) * C(3n, n)),
where t_k = C(6k, 3k) * C(3k, k).
Checks v_2(t_k) = 2 * s_2(k), v_2(S(n)), and v_2(a(n)) for 1 <= n <= 64.
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
    assert num % den == 0
    return num // den


def main() -> None:
    print("First 5 terms a(0..4):", [a(n) for n in range(5)])
    print("\n2-adic valuations for 1 <= n <= 32:")
    for n in range(1, 33):
        s_val = sum(t_term(k) * t_term(n - k) for k in range(n + 1))
        an = a(n)
        s2_n = n.bit_count()
        s2_3n = (3 * n).bit_count()
        print(
            f"  n={n:2d} (s2(n)={s2_n}, s2(3n)={s2_3n}): "
            f"v2(S(n))={v2(s_val):2d}, v2(C(3n,n))={v2(math.comb(3*n, n)):2d}, "
            f"v2(a(n))={v2(an):2d}, a(n)/8 odd={(an // 8) % 2 == 1}"
        )


if __name__ == "__main__":
    main()
