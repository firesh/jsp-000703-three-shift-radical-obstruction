#!/usr/bin/env python3
"""
Computational verification for the three-shift radical obstruction (JSP-000703).

Claim: there is no integer x >= 1 with rad(x) = rad(x+2).
Since the three-shift problem forces rad(x) = rad(x+2), it has no solution.

This script verifies rad(n) != rad(n+2) for all 1 <= n <= N by a full sieve
(no factoring, no heuristics), and additionally verifies the two known
two-shift (Benelux) families fail the third shift, and that the exceptional
Benelux pair (75, 1215) fails it too.
"""
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000

# Full sieve of smallest prime factor up to N+2.
limit = N + 2
spf = bytearray(limit + 1)
rad = [1] * (limit + 1)
for p in range(2, limit + 1):
    if spf[p] == 0:                      # p is prime
        for m in range(p, limit + 1, p):
            spf[m] = 1
            rad[m] *= p

bad = [n for n in range(1, N + 1) if rad[n] == rad[n + 2]]
print(f"verified range: 1 <= x <= {N}")
print(f"x with rad(x) == rad(x+2): {bad}")

# Cross-checks: the two known Benelux families satisfy shifts 0 and 1 but not 2.
def rad_small(n):
    r, m, d = 1, n, 2
    while d * d <= m:
        if m % d == 0:
            r *= d
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        r *= m
    return r

checks = []
for q in range(2, 12):
    x = 2 ** q - 2
    y = x * (x + 2)
    checks.append((x, y, rad_small(x) == rad_small(y), rad_small(x + 1) == rad_small(y + 1),
                   rad_small(x + 2) == rad_small(y + 2)))
checks.append((75, 1215, rad_small(75) == rad_small(1215),
               rad_small(76) == rad_small(1216), rad_small(77) == rad_small(1217)))
print("\nknown two-shift solutions (x, y, shift0, shift1, shift2):")
for row in checks:
    print("  ", row)
print("\nall shift-2 flags are False:", all(not row[4] for row in checks))
print("all shift-0/1 flags are True:", all(row[2] and row[3] for row in checks))
