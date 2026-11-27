#!/usr/bin/env python3
"""Explore J. Lowell's A001481 conjecture: for distinct sums of two squares a, b
with a + b = 2^k, search for pairs other than {0, 2^k}. Also tabulates the 2-adic
structure used in the proof (odd sums of two squares are 1 mod 4)."""
from math import isqrt

K = 24
N = 1 << K

sos = bytearray(N + 1)
for x in range(isqrt(N) + 1):
    for y in range(x, isqrt(N - x * x) + 1):
        sos[x * x + y * y] = 1

# Structural fact: every odd sum of two squares is 1 mod 4.
assert all(n % 4 == 1 for n in range(1, N + 1, 2) if sos[n])

exceptions = []
for k in range(K + 1):
    p = 1 << k
    for a in range(p // 2 + 1):
        b = p - a
        if a != b and sos[a] and sos[b] and a != 0:
            exceptions.append((a, b, k))
print(f"pairs a<b, a>0, a+b=2^k (k<={K}) with both sums of two squares: {exceptions}")
