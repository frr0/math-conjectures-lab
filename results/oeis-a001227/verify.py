#!/usr/bin/env python3
"""Deterministic check of Pol's A001227 conjecture for 1 <= n <= 3000, from the definitions:
a(n) = A067742(n) + 2*A131576(n) = A082647(n) + A131576(n)."""
from defs import a001227, a067742, a082647, a131576

N = 3000
for n in range(1, N + 1):
    a, m, e, o = a001227(n), a067742(n), a131576(n), a082647(n)
    assert a == m + 2 * e == o + e, (n, a, m, e, o)
print(f"OK: A001227 = A067742 + 2*A131576 = A082647 + A131576 for 1 <= n <= {N}")
