#!/usr/bin/env python3
"""Deterministic verifier for OEIS A238281 counterexamples n = 14 and n = 286."""

from __future__ import annotations


def is_prime(x: int) -> bool:
    if x < 2:
        return False
    if x in (2, 3):
        return True
    if x % 2 == 0 or x % 3 == 0:
        return False
    d = 5
    while d * d <= x:
        if x % d == 0 or x % (d + 2) == 0:
            return False
        d += 6
    return True


def count_primes_in_interval(a: int, b: int) -> int:
    return sum(1 for x in range(a + 1, b + 1) if is_prime(x))


def verify_counterexample(n: int) -> None:
    assert n > 1 and n != 8
    tested_candidates = 0
    for k in range(1, n):
        if is_prime(2 * k + 1):
            tested_candidates += 1
            c1 = count_primes_in_interval((k - 1) * n, k * n)
            c2 = count_primes_in_interval(k * n, (k + 1) * n)
            assert c1 != c2, f"Expected mismatch at n={n}, k={k}, but got c1={c1} == c2={c2}"
    assert tested_candidates > 0, f"No candidates found for n={n}"
    print(f"[verify] Verified counterexample n = {n} (all {tested_candidates} candidates failed).")


def main() -> None:
    # 1. Verify primary counterexample n = 14
    verify_counterexample(14)

    # 2. Verify second counterexample n = 286
    verify_counterexample(286)

    print("Verification of OEIS A238281 counterexamples succeeded.")


if __name__ == "__main__":
    main()
