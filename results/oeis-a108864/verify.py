#!/usr/bin/env python3
"""Independent verification of the counterexample m = 815634435 to OEIS A108864."""


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def divisors(n: int) -> list[int]:
    small, large = [], []
    d = 1
    while d * d <= n:
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
        d += 1
    return small + large[::-1]


def perfect_deficiency(n: int) -> int:
    rem = n
    for d in divisors(n):
        if d <= rem:
            rem -= d
    return rem


def main() -> None:
    factors = [3, 5, 7, 11, 547, 1291]
    assert all(is_prime(p) for p in factors)
    assert len(set(factors)) == len(factors)

    m = 1
    for p in factors:
        m *= p
    assert m == 815_634_435
    assert m > 1155
    assert m % 2 == 1

    divs = divisors(m)
    assert len(divs) == 64
    proper_sum = sum(divs[:-1])
    assert proper_sum == 815_634_429
    assert m - proper_sum == 6

    pd = perfect_deficiency(m)
    assert pd == 6
    assert pd <= 10

    # Also sanity-check 1155
    assert perfect_deficiency(1155) == 6

    print(
        f"Verified OEIS A108864 counterexample: m = {m} = {' * '.join(map(str, factors))} "
        f"(odd, > 1155, {len(divs)} divisors, perfectDeficiency = {pd} <= 10)."
    )


if __name__ == "__main__":
    main()
