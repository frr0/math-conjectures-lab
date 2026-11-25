#!/usr/bin/env python3
"""Verify Erdős-Straus parametric proofs (n % 8 != 1) and search remaining n <= 100_000."""

from __future__ import annotations

LIMIT = 100_000


def is_valid(n: int, x: int, y: int, z: int) -> bool:
    return x > 0 and y > 0 and z > 0 and 4 * x * y * z == n * (y * z + x * z + x * y)


def parametric_solution(n: int) -> tuple[int, int, int] | None:
    if n % 2 == 0:
        k = n // 2
        return (k, 2 * k, 2 * k)
    if n % 4 == 3:
        m = (n + 1) // 4
        return (m, 2 * m * n, 2 * m * n)
    if n % 8 == 5:
        m = (n + 3) // 8
        return (2 * m, 2 * m * n, m * n)
    return None


def find_solution(n: int) -> tuple[int, int, int]:
    """Find positive (x, y, z) with 4/n = 1/x + 1/y + 1/z."""
    sol = parametric_solution(n)
    if sol is not None:
        return sol

    # For n ≡ 1 (mod 8), search x in [ceil(n/4), ceil(3n/4)] and check if 4/n - 1/x = p/q
    # splits as 1/y + 1/z using standard divisor / greedy bounds.
    x_min = n // 4 + 1
    x_max = (3 * n) // 4 + 1
    for x in range(x_min, x_max + 1):
        # 4/n - 1/x = (4x - n) / (n * x) = num / den
        num = 4 * x - n
        den = n * x
        if num <= 0:
            continue
        # We need 1/y + 1/z = num / den  <=>  (num*y - den) | den^2
        # Quick check: try y = ceil(den / num) up to floor(2 * den / num)
        y_start = (den + num - 1) // num
        # Fast check for y_start and small offsets (covers almost all n immediately)
        for y in range(y_start, min(y_start + 50, (2 * den) // num + 1)):
            rem = num * y - den
            if rem > 0 and (den * y) % rem == 0:
                z = (den * y) // rem
                return (x, y, z)
    raise AssertionError(f"No Erdős-Straus solution found for n={n}")


def main() -> None:
    parametric_count = 0
    search_count = 0
    for n in range(2, LIMIT + 1):
        sol = parametric_solution(n)
        if sol is not None:
            assert is_valid(n, *sol), f"Parametric formula failed for n={n}: {sol}"
            parametric_count += 1
        else:
            sol = find_solution(n)
            assert is_valid(n, *sol), f"Search solution invalid for n={n}: {sol}"
            search_count += 1

    print(
        f"Verified Erdős-Straus for all 2 <= n <= {LIMIT} "
        f"({parametric_count} via parametric proof, {search_count} via search for n ≡ 1 mod 8)."
    )


if __name__ == "__main__":
    main()
