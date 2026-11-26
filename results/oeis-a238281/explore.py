#!/usr/bin/env python3
"""Computational exploration of OEIS A238281 conjecture_2."""

from __future__ import annotations


def sieve_primes(limit: int) -> list[bool]:
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for p in range(2, int(limit**0.5) + 1):
        if is_prime[p]:
            for m in range(p * p, limit + 1, p):
                is_prime[m] = False
    return is_prime


def main() -> None:
    MAX_N = 300
    UPPER = (MAX_N + 1) * MAX_N
    is_prime = sieve_primes(UPPER)

    prefix_primes = [0] * (UPPER + 1)
    for i in range(1, UPPER + 1):
        prefix_primes[i] = prefix_primes[i - 1] + (1 if is_prime[i] else 0)

    def count_primes(a: int, b: int) -> int:
        return prefix_primes[b] - prefix_primes[a]

    counterexamples = []
    for n in range(2, MAX_N + 1):
        if n == 8:
            continue
        found = False
        for k in range(1, n):
            if is_prime[2 * k + 1]:
                c1 = count_primes((k - 1) * n, k * n)
                c2 = count_primes(k * n, (k + 1) * n)
                if c1 == c2:
                    found = True
                    break
        if not found:
            counterexamples.append(n)
            print(f"[explore] Counterexample found at n = {n}")

    print(f"Total counterexamples for n <= {MAX_N}: {counterexamples}")


if __name__ == "__main__":
    main()
