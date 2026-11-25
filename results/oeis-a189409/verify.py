#!/usr/bin/env python3
"""Verify the counterexample to OEIS A189409 conjecture_1: 29^2 divides (p_9#)^2 + 1."""

from __future__ import annotations

import math

FIRST_NINE_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23)


def main() -> None:
    p9 = math.prod(FIRST_NINE_PRIMES)
    assert p9 == 223_092_870
    a9 = p9 * p9 + 1
    assert a9 == 49_770_428_644_836_901
    q, r = divmod(a9, 29 * 29)
    assert r == 0 and q == 59_180_057_841_661
    assert 29 * 29 * q == a9
    print(f"Verified counterexample: (p_9#)^2 + 1 = {a9} = 29^2 * {q} (not squarefree).")


if __name__ == "__main__":
    main()
