#!/usr/bin/env python3
"""Verify (and rediscover) the Lander-Parkin counterexample for Euler's k=5 conjecture."""

from __future__ import annotations


def verify_counterexample() -> None:
    a, b, c, d, e = 27, 84, 110, 133, 144
    assert all(x > 0 for x in (a, b, c, d, e))
    lhs = a**5 + b**5 + c**5 + d**5
    rhs = e**5
    assert lhs == rhs == 61_917_364_224, f"Mismatch: {lhs} != {rhs}"


def find_counterexample(limit: int = 150) -> tuple[int, int, int, int, int]:
    """Meet-in-the-middle search for a^5 + b^5 + c^5 + d^5 = e^5 with 1 <= a<=b<=c<=d < e <= limit."""
    pows = [i**5 for i in range(limit + 1)]
    pair_sums: dict[int, tuple[int, int]] = {}

    for a in range(1, limit + 1):
        pa = pows[a]
        for b in range(a, limit + 1):
            pair_sums.setdefault(pa + pows[b], (a, b))

    for e in range(2, limit + 1):
        pe = pows[e]
        for d in range(1, e):
            pd = pows[d]
            for c in range(1, d + 1):
                rem = pe - pd - pows[c]
                if rem in pair_sums:
                    a, b = pair_sums[rem]
                    if b <= c:
                        return (a, b, c, d, e)
    raise AssertionError(f"No counterexample found up to limit={limit}")


def main() -> None:
    verify_counterexample()
    sol = find_counterexample(150)
    assert sol == (27, 84, 110, 133, 144), f"Unexpected solution: {sol}"
    print(f"Verified counterexample: {sol[0]}^5 + {sol[1]}^5 + {sol[2]}^5 + {sol[3]}^5 = {sol[4]}^5")


if __name__ == "__main__":
    main()
