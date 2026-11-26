#!/usr/bin/env python3
"""Deterministic verifier for OEIS A046969 (Conjecture I).

Verifies:
1. Exact values of A046969(1..5) against the OEIS definition and Lean tests.
2. All primes 3 < p <= 100 with 2p - 1 prime satisfy:
   - p ≡ 1 (mod 6) and 2p + 1 is composite;
   - den(B_{2p}) == 6;
   - p divides num(B_{2p});
   - (2p - 1) does not divide num(B_{2p});
   - a(p) == 12 * (2p - 1), so a(p) / 12 == 2p - 1 is prime.
"""

from __future__ import annotations

from fractions import Fraction
import math


def bernoulli_table(max_m: int) -> list[Fraction]:
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


def a(n: int, b: list[Fraction]) -> int:
    if n == 0:
        return 0
    return (b[2 * n] / (2 * n * (2 * n - 1))).denominator


def main() -> int:
    max_p = 100
    b = bernoulli_table(2 * max_p)

    expected_prefix = {1: 12, 2: 360, 3: 1260, 4: 1680, 5: 1188}
    for idx, val in expected_prefix.items():
        got = a(idx, b)
        assert got == val, f"a({idx}) = {got}, expected {val}"

    checked = []
    for p in range(5, max_p + 1):
        if is_prime(p) and is_prime(2 * p - 1):
            q = 2 * p - 1
            assert p % 6 == 1, f"Expected p ≡ 1 (mod 6), got p={p}"
            assert not is_prime(2 * p + 1), f"Expected 2p+1 composite for p={p}"

            b2p = b[2 * p]
            assert b2p.denominator == 6, f"Expected den(B_{2*p}) = 6, got {b2p.denominator}"
            assert b2p.numerator % p == 0, f"Expected p | num(B_{2*p}) for p={p}"
            assert b2p.numerator % q != 0, f"Expected q ∤ num(B_{2*p}) for p={p}"

            ap = a(p, b)
            assert ap == 12 * q, f"Expected a({p}) = {12 * q}, got {ap}"
            assert ap % 12 == 0 and is_prime(ap // 12)
            checked.append(p)

    print(f"[oeis-a046969] Verified prefix a(1..5) and {len(checked)} primes p <= {max_p}: {checked}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
