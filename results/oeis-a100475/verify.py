#!/usr/bin/env python3
"""Verify the finite certificate for OEIS A100475 (no positive start ever loops)."""

from __future__ import annotations

import math

ROSSER_THRESHOLD = 22_027  # ceil(e^10) = 22027, where Rosser's theorem gives p_k > k ln k > 10k
EXACT_THRESHOLD = 6_473    # exact smallest K such that p_k >= 10k for all k >= K


def sieve_primes(limit: int) -> list[int]:
    is_p = bytearray(b"\x01") * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, math.isqrt(limit) + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = b"\x00" * ((limit - i * i) // i + 1)
    return [i for i, v in enumerate(is_p) if v]


def rev10(n: int) -> int:
    return int(str(n)[::-1])


def main() -> None:
    assert math.log(ROSSER_THRESHOLD) > 10.0
    # 22027th prime is 250,000-ish; sieve up to 300,000
    primes = sieve_primes(300_000)
    assert len(primes) >= ROSSER_THRESHOLD

    # 1. Confirm k = 6472 is the exact last index with p_k < 10k, and all k in [6473, 22027] satisfy p_k >= 10k
    assert primes[EXACT_THRESHOLD - 2] < 10 * (EXACT_THRESHOLD - 1)
    for k in range(EXACT_THRESHOLD, ROSSER_THRESHOLD + 1):
        p = primes[k - 1]
        assert p >= 10 * k, f"Failed p_k >= 10k at k={k}: p_k={p}"
        assert p % 10 != 0, f"Prime {p} ends in 0!"
        assert rev10(p) > k, f"Failed rev(p_k) > k at k={k}"

    # 2. Confirm every positive start x in [1, 6472] escapes to >= 6473 in <= 9 steps
    max_steps = 0
    for x in range(1, EXACT_THRESHOLD):
        cur = x
        steps = 0
        while cur < EXACT_THRESHOLD:
            cur = rev10(primes[cur - 1])
            steps += 1
            assert steps <= 20, f"Orbit from x={x} failed to escape!"
        max_steps = max(max_steps, steps)

    print(
        f"Verified OEIS A100475: p_k >= 10k for all {EXACT_THRESHOLD} <= k <= {ROSSER_THRESHOLD} "
        f"(Rosser covers k >= {ROSSER_THRESHOLD}), and all 1 <= x < {EXACT_THRESHOLD} escape in <= {max_steps} steps."
    )


if __name__ == "__main__":
    main()
