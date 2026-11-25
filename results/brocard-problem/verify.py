#!/usr/bin/env python3
"""Exact search and verification for Brocard's Problem (n! + 1 = m^2) for 1 <= n <= 1000."""

from __future__ import annotations

import math

LIMIT = 1000


def main() -> None:
    solutions: list[tuple[int, int]] = []
    fact = 1
    for n in range(1, LIMIT + 1):
        fact *= n
        target = fact + 1
        root = math.isqrt(target)
        if root * root == target:
            solutions.append((n, root))
            if n >= 5:
                assert root % 10 in (1, 9), f"Last-digit theorem violated for ({n}, {root})"

    expected = [(4, 5), (5, 11), (7, 71)]
    assert solutions == expected, f"Unexpected solutions up to {LIMIT}: {solutions}"
    print(f"Verified Brocard's Problem for 1 <= n <= {LIMIT}: unique solutions {solutions}.")


if __name__ == "__main__":
    main()
