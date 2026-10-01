# regla296 — Hilbert functions of the point sets A (all), B (Hodge), T (non-Hodge) in P(V)(F_p), V = {sum a_i = 0} in F_p^N, N = n+2.
#   full  : E_full  = sum_j [h_B(j) + h_T(j) - h_A(j)]                      (= dim S/(I(B)+I(T)))
#   short : E_short = 2 sum_{j<m} h_B(j) + h_B(m) - Isp + 1,  m = k(p-2)-1,  Isp = dim of the Sp_{p-1}-invariants of (F^{p-1})^{(x) 2k+2}
# Usage: python3 hilbert2.py n p full|short [Jmax]
import sys, itertools, time
import numpy as np
from collections import Counter
from math import factorial
n, p, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
k = n // 2; N = n + 2; nv = N - 2; m = k * (p - 2) - 1; t0 = time.time()
Jmax = int(sys.argv[4]) if len(sys.argv) > 4 else None
# ---- points, normalised x_1 = 1; coordinates x_1..x_{N-1}, x_0 = -sum
import os
def all_matchings(pts):
    if not pts: yield []; return
    a0_ = pts[0]
    for i in range(1, len(pts)):
        for rest in all_matchings(pts[1:i] + pts[i+1:]): yield [(a0_, pts[i])] + rest
SUB = None
if os.environ.get('SUBJ'):
    allJ = list(all_matchings(list(range(N)))); SUB = [allJ[int(i)] for i in os.environ['SUBJ'].split(',')]; print('SUBFAMILY of matchings:', SUB, flush=True)
def gen_points():
    A = []; isB = []
    for a in itertools.product(range(1, p), repeat=N - 2):
        a = (1,) + a; a0 = (-sum(a)) % p
        if a0 == 0: continue
        full = (a0,) + a
        if SUB is None: c = Counter(full); ok = all(c[v] == c[p - v] for v in c)
        else: ok = any(all((full[x] + full[y]) % p == 0 for x, y in J) for J in SUB)
        A.append(a[1:]); isB.append(ok)
    return np.array(A, dtype=np.int64), np.array(isB)
def gen_B_only():
    # pairable zero-free vectors with x_1 = 1: built from the matchings, to avoid the full enumeration
    out = set()
    def matchings(pts):
        if not pts: yield []; return
        a = pts[0]
        for i in range(1, len(pts)):
            for rest in matchings(pts[1:i] + pts[i+1:]): yield [(a, pts[i])] + rest
    for J in matchings(list(range(N))):
        for vals in itertools.product(range(1, p), repeat=k + 1):
            x = [0] * N
            for (a, b), v in zip(J, vals): x[a] = v; x[b] = (-v) % p
            inv = pow(x[1], -1, p); out.add(tuple((inv * xi) % p for xi in x[2:]))
    return np.array(sorted(out), dtype=np.int64)
if mode == 'short':
    if (p - 1) ** (N - 2) <= 3_000_000:
        PA, isB = gen_points(); PB = PA[isB]; del PA
    else:
        PB = gen_B_only()
    sets = {'B': PB}
else:
    PA, isB = gen_points(); sets = {'A': PA, 'B': PA[isB], 'T': PA[~isB]}
print(f'(n,p)=({n},{p}) mode={mode}  points: ' + '  '.join(f'{s} {len(v)}' for s, v in sets.items()) + f'   m={m}', flush=True)
def monomials(deg):
    # exponent vectors of exact degree deg in nv variables, each exponent <= p-2 (x^(p-1) = 1 on non-zero coordinates)
    def rec(i, left):
        if i == nv - 1:
            if left <= p - 2: yield (left,)
            return
        for e in range(min(left, p - 2) + 1):
            for r in rec(i + 1, left - e): yield (e,) + r
    if nv == 0:
        if deg == 0: yield ()
        return
    yield from rec(0, deg)
def hilbert(P, J, stop_full=True):
    npts = len(P); DT = np.float32 if npts * (p - 1) ** 2 < 2 ** 24 else np.float64
    pw = np.ones((p, npts, nv), dtype=np.int64)
    for e in range(1, p): pw[e] = (pw[e - 1] * P) % p
    BF = np.zeros((npts, npts), dtype=DT); piv = []; h = []; rank = 0
    for deg in range(J + 1):
        if rank < npts:
            mons = list(monomials(deg))
            for c0 in range(0, len(mons), 512):
                chunk = mons[c0:c0 + 512]; R = np.ones((len(chunk), npts), dtype=np.int64)
                for i, ex in enumerate(chunk):
                    for v, e in enumerate(ex):
                        if e: R[i] = (R[i] * pw[e][:, v]) % p
                R = R.astype(DT)
                if rank: R = np.mod(R - R[:, piv] @ BF[:rank], p)
                newrows = []; newpiv = []
                for i in range(len(chunk)):
                    nzc = np.flatnonzero(R[i])
                    if nzc.size == 0: continue
                    c = int(nzc[0]); R[i] = np.mod(R[i] * pow(int(R[i, c]), -1, p), p)
                    col = R[:, c].copy(); col[i] = 0; nzr = np.flatnonzero(col)
                    if nzr.size: R[nzr] = np.mod(R[nzr] - np.outer(col[nzr], R[i]), p)
                    newrows.append(i); newpiv.append(c)
                if newrows:
                    Rn = R[newrows]
                    for b0 in range(0, rank, 1024):
                        blk = BF[b0:min(b0 + 1024, rank)]
                        blk -= blk[:, newpiv] @ Rn; np.mod(blk, p, out=blk)
                    BF[rank:rank + len(newrows)] = Rn; piv += newpiv; rank += len(newrows)
                if rank == npts: break
        h.append(rank)
        if stop_full and rank == npts and Jmax is None and mode == 'full': pass
    return h
def f_shape(lam):
    # number of standard Young tableaux of shape lam (hook length formula)
    lam = [x for x in lam if x]; nn = sum(lam); conj = [sum(1 for x in lam if x > j) for j in range(lam[0])] if lam else []
    prod = 1
    for i, r in enumerate(lam):
        for j in range(r): prod *= (r - j - 1) + (conj[j] - i - 1) + 1
    return factorial(nn) // prod
def partitions(nn, maxpart=None):
    if maxpart is None: maxpart = nn
    if nn == 0: yield []; return
    for a in range(min(nn, maxpart), 0, -1):
        for r in partitions(nn - a, a): yield [a] + r
def Isp():
    r = (p - 1) // 2; tot = 0
    for mu in partitions(k + 1):
        if mu[0] > r: continue
        lam2 = [2 * x for x in mu]; conj = [sum(1 for x in lam2 if x > j) for j in range(lam2[0])]
        tot += f_shape(conj)
    return tot
sigma = n * (p - 2) - 2
if mode == 'short':
    hB = hilbert(sets['B'], m); I = Isp()
    E = 2 * sum(hB[:m]) + hB[m] - I + 1
    print(' h_B(0..m) =', hB); print(f' Isp = {I}')
    print(f'RESULT short (n,p)=({n},{p}): E = {E}   [socle degree {sigma}]   t={time.time()-t0:.1f}s')
else:
    J = Jmax if Jmax is not None else sigma + 1
    hs = {s: hilbert(v, J) for s, v in sets.items()}
    term = [hs['B'][j] + hs['T'][j] - hs['A'][j] for j in range(J + 1)]
    for s in 'ABT': print(f' h_{s} =', hs[s])
    print(' term =', term)
    full = all(hs[s][-1] == len(sets[s]) for s in 'ABT')
    I = Isp(); hB = hs['B']; Es = 2 * sum(hB[:m]) + hB[m] - I + 1 if J >= m else None
    print(f' saturated at J={J}: {full}   palindromic: {term[:sigma+1] == term[:sigma+1][::-1] if J >= sigma else "n/a"}   Isp = {I}   h_A(m)-h_T(m) = {hs["A"][m]-hs["T"][m] if J>=m else "n/a"}')
    print(f'RESULT full (n,p)=({n},{p}): E_full = {sum(term)}   E_short = {Es}   t={time.time()-t0:.1f}s')
print('FIN-OK')
