#!/usr/bin/env python3
"""
Exhaustive sanity check: search all pairs 1 <= x < y <= B for the three-shift
condition and print any hit.  This is a direct check of the *pair* statement,
independent of the reduction used in the proof.
"""
import sys, math

B = int(sys.argv[1]) if len(sys.argv) > 1 else 3000

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

R = [0] + [rad(n) for n in range(1, B + 3)]

hits = []
two_shift = []
for x in range(1, B + 1):
    for y in range(x + 1, B + 1):
        if R[x] == R[y] and R[x + 1] == R[y + 1]:
            two_shift.append((x, y, R[x + 2] == R[y + 2]))
            if R[x + 2] == R[y + 2]:
                hits.append((x, y))

print(f"pairs 1 <= x < y <= {B}")
print(f"two-shift solutions found: {len(two_shift)}")
for x, y, third in two_shift[:20]:
    print(f"   x={x}, y={y}, third shift satisfied: {third}")
print(f"three-shift solutions found: {hits}")
