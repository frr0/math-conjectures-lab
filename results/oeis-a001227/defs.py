"""Brute-force definitions of the four OEIS sequences, straight from their names."""


def runs(n: int) -> list[tuple[int, int]]:
    """All (start m >= 1, length k >= 1) with m + (m+1) + ... + (m+k-1) = n."""
    out = []
    k = 1
    while k * (k + 1) // 2 <= n:
        rest = n - k * (k - 1) // 2  # = k*m
        if rest % k == 0 and rest // k >= 1:
            out.append((rest // k, k))
        k += 1
    return out


def a001227(n: int) -> int:  # number of odd divisors of n
    return sum(1 for d in range(1, n + 1, 2) if n % d == 0)


def a067742(n: int) -> int:  # divisors d with sqrt(n/2) <= d < sqrt(2n)
    return sum(1 for d in range(1, n + 1) if n % d == 0 and n <= 2 * d * d < 4 * n)


def a131576(n: int) -> int:  # sums of an even number of consecutive positive integers
    return sum(1 for _, k in runs(n) if k % 2 == 0)


def a082647(n: int) -> int:  # divisors d of n s.t. n is a sum of d consecutive positive integers
    return sum(1 for _, k in runs(n) if n % k == 0)
