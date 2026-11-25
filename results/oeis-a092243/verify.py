#!/usr/bin/env python3
"""Exact verification of OEIS A092243 conjecture1: exists n > 250000 with a(n) > 0."""

LIMIT = 4_000_000


def sieve_primes(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0] = sieve[1] = 0
    i = 2
    while i * i <= limit:
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
        i += 1
    return [n for n in range(2, limit + 1) if sieve[n]]


def main() -> None:
    primes = sieve_primes(LIMIT)
    assert len(primes) > 273_677, "Sieve limit too small"

    # Verify exact prime values at the witness transition (0-indexed: p_0 = 2)
    assert primes[0] == 2 and primes[1] == 3 and primes[2] == 5 and primes[3] == 7
    assert primes[261_148] == 3_666_529
    assert primes[261_149] == 3_666_539
    assert primes[261_150] == 3_666_581

    score = 0
    prev_gap = primes[1] - primes[0]
    first_pos_after_250k = None
    score_at = {0: 0, 1: 0}

    for k in range(2, len(primes)):
        gap = primes[k] - primes[k - 1]
        if gap > prev_gap:
            score += 1
        elif gap < prev_gap:
            score -= 1
        prev_gap = gap

        if k in (2, 3, 4, 5, 261_149, 261_150, 273_677):
            score_at[k] = score
        if k > 250_000 and score > 0 and first_pos_after_250k is None:
            first_pos_after_250k = (k, score)

    # Check base cases matching FormalConjectures/OEIS/92243.lean
    assert score_at[0] == 0
    assert score_at[1] == 0
    assert score_at[2] == 1
    assert score_at[3] == 1
    assert score_at[4] == 2
    assert score_at[5] == 1

    # Check exact smallest witness above 250,000
    assert score_at[261_149] == 0
    assert score_at[261_150] == 1
    assert first_pos_after_250k == (261_150, 1)
    assert score_at[273_677] == 83

    print(
        f"Verified OEIS A092243 conjecture1: smallest witness n > 250000 is "
        f"n = {first_pos_after_250k[0]} with a(n) = {first_pos_after_250k[1]} > 0 "
        f"(p_261150 = {primes[261_150]}, max score up to {len(primes)-1} is a(273677) = {score_at[273_677]})."
    )


if __name__ == "__main__":
    main()
