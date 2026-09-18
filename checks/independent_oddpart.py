#!/usr/bin/env python3
"""
Second, independent check with a different algorithm and a different criterion.

Criterion used: if rad(x) == rad(x+2) with x even, then oddpart(x) = oddpart(x+2) = 1
must hold (both numbers are powers of two).  We enumerate every x up to B whose odd part
and the odd part of x+2 are both 1, which is necessary for rad(x) == rad(x+2), and then
verify the radicals exactly.  No sieve is used.
"""
import sys

B = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 7

def oddpart(n):
    while n % 2 == 0:
        n //= 2
    return n

def rad(n):
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

candidates = [x for x in range(2, B + 1, 2) if oddpart(x) == 1 and oddpart(x + 2) == 1]
print(f"x <= {B} with oddpart(x) = oddpart(x+2) = 1: {candidates}")
print("exact radical check on those candidates:",
      [(x, rad(x), rad(x + 2), rad(x) == rad(x + 2)) for x in candidates])
