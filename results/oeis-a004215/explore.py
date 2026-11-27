#!/usr/bin/env python3
"""Explore A004215 vs A023105: tabulate both counts and check Legendre's form
4^a(8b+7) and the shared recurrence X(m+3) = 2^m + X(m+1)."""
def legendre(n):
    while n and n % 4 == 0: n //= 4
    return n % 8 == 7

C = [sum(legendre(n) for n in range(1, 1 << m)) for m in range(23)]
Q = [len({x * x % (1 << m) for x in range(1 << m)}) for m in range(21)]
for m in range(1, 21):
    print(m, C[m], Q[m], C[m] == Q[m] - 2)
assert all(C[m + 3] == 2**m + C[m + 1] for m in range(20))
assert all(Q[m + 3] == 2**m + Q[m + 1] for m in range(18))
