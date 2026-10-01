#!/usr/bin/env python3
# Cold reader's own lattice engine (independent of the group-ring computations).
# usage: cold_lattice.py n p [one]
# Standard k-spaces of the Fermat variety z_0^p+...+z_{N-1}^p=0:  for a matching J and odd exponents b,
#   z_k = w^b z_j  for each pair (j<k) of J,  w = exp(i*pi/p)  (so (w^b)^p = -1).
# P.P' = (1 - (1-p)^c)/p,  c-1 = dim(P ∩ P')  (c = number of compatible cycles of J ∪ J').
import sys, itertools
import numpy as np
n = int(sys.argv[1]); p = int(sys.argv[2]); ONE = len(sys.argv) > 3
k = n // 2; N = 2 * k + 2
M = 1
while p ** (M + 1) < 3.0e9: M += 1
PM = p ** M

def matchings(items):
    if not items: yield []; return
    a = items[0]
    for i in range(1, len(items)):
        b = items[i]; rest = items[1:i] + items[i + 1:]
        for m in matchings(rest): yield [(a, b)] + m

Js = list(matchings(list(range(N))))
if ONE: Js = Js[:1]
spaces = []
for J in Js:
    for bs in itertools.product(range(1, 2 * p, 2), repeat=k + 1):
        nb = [None] * N                       # nb[v] = (partner, exponent e) meaning z_partner = w^e z_v
        for (j, kk), b in zip(J, bs):
            nb[j] = (kk, b); nb[kk] = (j, (-b) % (2 * p))
        spaces.append(nb)
S = len(spaces)
print(f"n={n} p={p} k={k}: {len(Js)} matching(s), {S} standard spaces", flush=True)

def ccount(P, Q):
    seen = [False] * N; c = 0
    for s in range(N):
        if seen[s]: continue
        v = s; e = 0
        while True:                            # alternate a P-edge and a Q-edge
            seen[v] = True
            u, b = P[v]; e += b; seen[u] = True
            v, b2 = Q[u]; e += b2
            if v == s: break
        if e % (2 * p) == 0: c += 1
    return c

val = [(1 - (1 - p) ** c) // p for c in range(k + 2)]
G = np.zeros((S, S), dtype=np.int64)
for i in range(S):
    Pi = spaces[i]
    for j in range(i, S):
        G[i, j] = G[j, i] = val[ccount(Pi, spaces[j])]
print("self-intersection:", int(G[0, 0]), " (expected", val[k + 1], ")", flush=True)

def smith_vals(Mx, q, Mq):
    QM = q ** Mq
    A = Mx % QM; rows, cols = A.shape; vals = []; t0 = 0
    for c in range(cols):
        sub = A[t0:, c:]
        v = 0; found = None
        while v < Mq:
            nz = np.argwhere(sub % (q ** (v + 1)) != 0)
            if len(nz): found = nz[0]; break
            v += 1
        if found is None: break
        i, j = int(found[0]) + t0, int(found[1]) + c
        if i != t0: A[[t0, i]] = A[[i, t0]]
        if j != c: A[:, [c, j]] = A[:, [j, c]]
        unit = int(A[t0, c]) // (q ** v)
        A[t0] = (A[t0] * pow(unit, -1, QM)) % QM
        f = (A[t0 + 1:, c] // (q ** v)) % QM
        nzr = np.nonzero(f)[0]
        if len(nzr): A[t0 + 1 + nzr] = (A[t0 + 1 + nzr] - (f[nzr, None] * A[t0][None, :]) % QM) % QM
        vals.append(v); t0 += 1
        if t0 == rows: break
    return vals

vals = smith_vals(G, p, M)
hist = {v: vals.count(v) for v in sorted(set(vals))}
print(f"rank (p-adic pivots with valuation < {M}): {len(vals)}")
print(f"elementary divisors, p-part: " + " . ".join(f"{p**v}^{m}" for v, m in hist.items()))
print(f"v_p(disc) = {sum(vals)}")
for q in (2, 3, 5, 7):
    if q == p: continue
    Mq = 1
    vq = smith_vals(G, q, 4)
    print(f"  prime {q}: rank {len(vq)}, v_{q}(disc) = {sum(vq)}")
print("COLD-DONE")
