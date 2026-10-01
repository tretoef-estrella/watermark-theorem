# regla296 — TEST of the point-set formula
#   E(n,p) ?= sum_j [ h_B(j) + h_T(j) - h_A(j) ] = dim_{F_p} S / ( I(B) + I(T) ),
# where A = points of P(V)(F_p), V = {a in F_p^N : sum a_i = 0}, N = n+2, with all a_i != 0,
#       B = the pairable ones (Hodge), T = A \ B, and h_X(j) = Hilbert function of the point set X in degree j.
# Usage: python3 hilbert_puntos.py n p
import sys, itertools, time
import numpy as np
from collections import Counter
n, p = int(sys.argv[1]), int(sys.argv[2]); N = n + 2; d = n + 1; t0 = time.time()
def rank_mod(M, p):
    M = M.copy() % p; r = 0; rows, cols = M.shape
    for c in range(cols):
        if r == rows: break
        piv = np.nonzero(M[r:, c])[0]
        if piv.size == 0: continue
        i = r + int(piv[0])
        if i != r: M[[r, i]] = M[[i, r]]
        M[r] = (M[r] * pow(int(M[r, c]), -1, p)) % p
        nz = np.nonzero(M[:, c])[0]; nz = nz[nz != r]
        if nz.size: M[nz] = (M[nz] - np.outer(M[nz, c], M[r])) % p
        r += 1
    return r
A = []; isB = []
for a in itertools.product(range(1, p), repeat=d - 1):
    a = (1,) + a; a0 = (-sum(a)) % p
    if a0 == 0: continue
    c = Counter(a + (a0,)); A.append(a); isB.append(all(c[v] == c[p - v] for v in c))
A = np.array(A, dtype=np.int64); isB = np.array(isB)
nA, nB, nT = len(A), int(isB.sum()), int((~isB).sum())
print(f'(n,p)=({n},{p})  points: A {nA}  B {nB}  T {nT}', flush=True)
# monomials of degree j in y_1..y_d with exponents of y_2..y_d at most p-1 (y_i^p y_1 = y_i y_1^p on F_p-points)
pw = np.ones((p, nA, d), dtype=np.int64)
for e in range(1, p): pw[e] = (pw[e - 1] * A) % p
def evalmat(j):
    cols = []
    for ex in itertools.product(range(p), repeat=d - 1):
        s = sum(ex)
        if s > j: continue
        col = np.ones(nA, dtype=np.int64)        # y_1 = 1 on every point
        for i, e in enumerate(ex):
            if e: col = (col * pw[e][:, i + 1]) % p
        cols.append(col)
    return np.array(cols, dtype=np.int64).T
E = 0; j = 0
while True:
    M = evalmat(j)
    hA = rank_mod(M, p); hB = rank_mod(M[isB], p); hT = rank_mod(M[~isB], p)
    E += hB + hT - hA
    print(f'   j={j:2d}  h_A={hA}  h_B={hB}  h_T={hT}   term={hB+hT-hA}   E so far={E}   t={time.time()-t0:.1f}s', flush=True)
    if hA == nA and hB == nB and hT == nT: break
    j += 1
print(f'RESULT (n,p)=({n},{p}): sum_j [h_B+h_T-h_A] = {E}')
print('FIN-OK')
