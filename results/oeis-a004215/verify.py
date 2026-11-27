#!/usr/bin/env python3
"""Deterministic check of Neumann's A004215 conjecture for 1 <= m <= 16.
Directly from the definitions (no Legendre theorem used): count n < 2^m needing
exactly 4 nonzero squares; compare with #{x^2 mod 2^m} - 2 and with the closed
form floor((2^m+10)/6) - 2 proved in README.md / Lean."""
from math import isqrt

M = 16
N = 1 << M
sq = [i * i for i in range(1, isqrt(N) + 1)]
is1 = bytearray(N); [is1.__setitem__(s, 1) for s in sq if s < N]
is2 = bytearray(N)
for s in sq:
    for t in sq:
        if s + t < N: is2[s + t] = 1
is3 = bytearray(N)
for n in range(N):
    if is2[n]:
        for s in sq:
            if n + s >= N: break
            is3[n + s] = 1
needs4 = [n >= 1 and not (is1[n] or is2[n] or is3[n]) for n in range(N)]

for m in range(1, M + 1):
    count = sum(needs4[:1 << m])
    residues = len({x * x % (1 << m) for x in range(1 << m)})
    assert count == residues - 2 == (2**m + 10) // 6 - 2, (m, count, residues)
print(f"OK: #A004215 terms < 2^m == A023105(m) - 2 for 1 <= m <= {M}")
