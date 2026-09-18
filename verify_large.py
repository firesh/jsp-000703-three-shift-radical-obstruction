#!/usr/bin/env python3
"""Full-sieve verification of rad(n) != rad(n+2) for 1 <= n <= N (exact radicals)."""
import sys, array
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**8
lim = N + 2
rad = array.array('Q', [1]) * (lim + 1)
sieve = bytearray(lim + 1)
for p in range(2, lim + 1):
    if not sieve[p]:
        pk = p
        for m in range(p, lim + 1, p):
            sieve[m] = 1
            rad[m] *= pk
hits = [n for n in range(1, N + 1) if rad[n] == rad[n + 2]]
print("x <= ", N, " with rad(x)==rad(x+2):", hits)
