#!/usr/bin/env python3
# Cold reader's lattice engine, version 2: same mathematics as cold_lattice.py, Gram built block by block
# (pair of matchings at a time) with numpy, and a leaner p-adic Smith form (in place, block-wise pivot search).
# usage: cold_lattice2.py n p [one] ; env MEXP = exponent M of the modulus p^M (default: largest with p^M < 3e9)
import sys, os, itertools
import numpy as np
n = int(sys.argv[1]); p = int(sys.argv[2]); ONE = len(sys.argv) > 3
k = n // 2; N = 2 * k + 2
M = 1
while p ** (M + 1) < 3.0e9: M += 1
M = int(os.environ.get("MEXP", M)); PM = p ** M

def matchings(items):
    if not items: yield []; return
    a = items[0]
    for i in range(1, len(items)):
        b = items[i]; rest = items[1:i] + items[i + 1:]
        for m in matchings(rest): yield [(a, b)] + m
Js = list(matchings(list(range(N))))
if ONE: Js = Js[:1]
bs = np.array(list(itertools.product(range(1, 2 * p, 2), repeat=k + 1)), dtype=np.int64)   # (p^{k+1}, k+1)
nb = bs.shape[0]; S = len(Js) * nb
print(f"n={n} p={p} k={k}: {len(Js)} matching(s), {S} standard spaces, modulus p^{M}", flush=True)
val = np.array([(1 - (1 - p) ** c) // p for c in range(k + 2)], dtype=np.int64)
G = np.zeros((S, S), dtype=np.int64)
for a, J in enumerate(Js):
    partJ = {}
    for idx, (j, kk) in enumerate(J): partJ[j] = (kk, idx, +1); partJ[kk] = (j, idx, -1)   # z_kk = w^{b} z_j
    for b_, Q in enumerate(Js):
        if b_ < a: continue
        partQ = {}
        for idx, (j, kk) in enumerate(Q): partQ[j] = (kk, idx, +1); partQ[kk] = (j, idx, -1)
        seen = [False] * N
        cnt = np.zeros((nb, nb), dtype=np.int64)
        for s in range(N):
            if seen[s]: continue
            cJ = np.zeros(k + 1, dtype=np.int64); cQ = np.zeros(k + 1, dtype=np.int64)
            v = s
            while True:
                seen[v] = True
                u, idx, sg = partJ[v]; cJ[idx] += sg; seen[u] = True
                v, idx, sg = partQ[u]; cQ[idx] += sg
                if v == s: break
            eJ = (bs @ cJ) % (2 * p); eQ = (bs @ cQ) % (2 * p)
            cnt += ((eJ[:, None] + eQ[None, :]) % (2 * p) == 0)
        blk = val[cnt]
        G[a * nb:(a + 1) * nb, b_ * nb:(b_ + 1) * nb] = blk
        if b_ != a: G[b_ * nb:(b_ + 1) * nb, a * nb:(a + 1) * nb] = blk.T
print("self-intersection:", int(G[0, 0]), "(expected", int(val[k + 1]), "); symmetric:", bool((G == G.T).all()), flush=True)

def smith_inplace(A, q, Mq):
    QM = q ** Mq
    np.remainder(A, QM, out=A)
    rows, cols = A.shape; vals = []; t0 = 0; BL = 512
    while t0 < min(rows, cols):
        found = None
        for v in range(Mq):
            qq = q ** (v + 1)
            for r0 in range(t0, rows, BL):
                blk = A[r0:r0 + BL, t0:]
                nz = np.argwhere(blk % qq != 0)
                if len(nz): found = (r0 + int(nz[0][0]), t0 + int(nz[0][1]), v); break
            if found: break
        if not found: break
        i, j, v = found
        if i != t0: A[[t0, i]] = A[[i, t0]]
        if j != t0: A[:, [t0, j]] = A[:, [j, t0]]
        unit = int(A[t0, t0]) // (q ** v)
        A[t0] = (A[t0] * pow(unit, -1, QM)) % QM
        f = (A[t0 + 1:, t0] // (q ** v)) % QM
        nzr = np.nonzero(f)[0]
        row = A[t0].copy()
        for r0 in range(0, len(nzr), BL):
            ii = t0 + 1 + nzr[r0:r0 + BL]
            A[ii, t0:] = (A[ii, t0:] - (f[nzr[r0:r0 + BL], None] * row[None, t0:]) % QM) % QM
        vals.append(v); t0 += 1
    return vals

vals = smith_inplace(G, p, M)
hist = {v: vals.count(v) for v in sorted(set(vals))}
print(f"rank (p-adic pivots with valuation < {M}): {len(vals)}")
print("elementary divisors, p-part: " + " . ".join(f"{p**v}^{m}" for v, m in hist.items()))
print(f"v_p(disc) = {sum(vals)}")
print("COLD-DONE")
