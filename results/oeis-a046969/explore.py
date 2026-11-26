#!/usr/bin/env python3
"""Computational exploration of OEIS A046969 (Conjecture I).

OEIS A046969(n) = den(B_{2n} / (2n * (2n - 1))), where B_m is the m-th Bernoulli number.
Conjecture I (Lorenzo Sauras Altuzarra, 2020):
For every prime p > 3 such that 2p - 1 is also prime (OEIS A005382),
a(p) / 12 is prime (in fact, a(p) / 12 = 2p - 1).
"""

from __future__ import annotations

from fractions import Fraction
import math


def bernoulli_table(max_m: int) -> list[Fraction]:
    """Compute exact Bernoulli numbers B_0, ..., B_{max_m} using the standard recurrence."""
    b = [Fraction(0)] * (max_m + 1)
    b[0] = Fraction(1)
    for m in range(1, max_m + 1):
        total = Fraction(0)
        for k in range(m):
            total += math.comb(m + 1, k) * b[k]
        b[m] = -total / (m + 1)
    return b


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


def main() -> None:
    max_p = 100
    b = bernoulli_table(2 * max_p)

    print("First 10 terms of A046969:")
    first_10 = [(b[2 * n] / (2 * n * (2 * n - 1))).denominator for n in range(1, 11)]
    print(" ", first_10)

    print(f"\nChecking all primes 3 < p <= {max_p} with 2p - 1 prime:")
    for p in range(5, max_p + 1):
        if is_prime(p) and is_prime(2 * p - 1):
            b2p = b[2 * p]
            term = b2p / (2 * p * (2 * p - 1))
            ap = term.denominator
            q = 2 * p - 1
            print(
                f"  p={p:3d}, q=2p-1={q:3d}, den(B_{{2p}})={b2p.denominator}, "
                f"p|num={b2p.numerator % p == 0}, q|num={b2p.numerator % q == 0}, "
                f"a(p)={ap}, a(p)/12={ap // 12}"
            )


if __name__ == "__main__":
    main()
