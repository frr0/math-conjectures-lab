#!/usr/bin/env python3
"""Deterministic finite check of the A001481 power-of-two statement for k <= 20.
The full statement is proved in README.md and Lean (lean/ConjectureLab/OeisA001481.lean)."""
from math import isqrt

K = 20
N = 1 << K
sos = bytearray(N + 1)
for x in range(isqrt(N) + 1):
    for y in range(x, isqrt(N - x * x) + 1):
        sos[x * x + y * y] = 1

for k in range(K + 1):
    p = 1 << k
    assert sos[p], f"2^{k} should be a sum of two squares"
    for a in range(1, p):
        b = p - a
        if a != b and sos[a] and sos[b]:
            raise SystemExit(f"Unexpected pair {a} + {b} = 2^{k}")
print(f"OK: for k <= {K}, only {{0, 2^k}} splits 2^k into distinct sums of two squares.")
