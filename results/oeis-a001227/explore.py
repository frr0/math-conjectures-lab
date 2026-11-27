#!/usr/bin/env python3
"""Explore Pol's A001227 identities; compare our definitions with OEIS data."""
from defs import a001227, a067742, a082647, a131576

OEIS = {  # first 30 terms from oeis.org
    a001227: [1,1,2,1,2,2,2,1,3,2,2,2,2,2,4,1,2,3,2,2,4,2,2,2,3,2,4,2,2,4],
    a067742: [1,1,0,1,0,2,0,1,1,0,0,2,0,0,2,1,0,1,0,2,0,0,0,2,1,0,0,2,0,2],
    a131576: [0,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,2,1,1,0,1,1,2,0,1,1],
    a082647: [1,1,1,1,1,2,1,1,2,1,1,2,1,1,3,1,1,2,1,2,2,1,1,2,2,1,2,2,1,3],
}
for f, data in OEIS.items():
    assert [f(n) for n in range(1, 31)] == data, f.__name__
print("definitions match OEIS data for n <= 30")

# Structural pattern behind the proof: odd divisors d split by d^2 < 2n vs d^2 > 2n.
for n in range(1, 41):
    odd = [d for d in range(1, n + 1, 2) if n % d == 0]
    A = sum(1 for d in odd if d * d < 2 * n)
    B = sum(1 for d in odd if d * d > 2 * n)
    assert (A, B) == (a082647(n), a131576(n)) and a067742(n) == A - B
    print(f"n={n:3d} odd={odd} A={A} B={B} middle={a067742(n)}")
