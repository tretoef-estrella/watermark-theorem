# regla296 — p-part of the elementary divisors of the lattice L(X) spanned by the linear k-spaces
# of the Fermat variety of dimension n = 2k and odd prime degree p.
#   space (J, gamma): x_b = -zeta^{gamma_i} x_a for the i-th pair (a<b) of the perfect matching J
#   P.P' = (1 - (1-p)^{c}) / p,   c = number of cycles of J u J' on which the two systems agree (= dim(P n P') + 1)
# Usage: python3 gram_smith.py n p [M]
import sys, itertools, time
import numpy as np
n, p = int(sys.argv[1]), int(sys.argv[2]); M = int(sys.argv[3]) if len(sys.argv) > 3 else 8
k = n // 2; N = n + 2; t0 = time.time()
def matchings(pts):
    if not pts: yield []; return
    a = pts[0]
    for i in range(1, len(pts)):
        b = pts[i]
        for rest in matchings(pts[1:i] + pts[i+1:]): yield [(a, b)] + rest
Js = list(matchings(list(range(N))))
import os
if os.environ.get('SUBJ'):
    Js = [Js[int(i)] for i in os.environ['SUBJ'].split(',')]; print('SUBFAMILY of matchings:', Js, flush=True)
nJ = len(Js); B = p ** (k + 1); NN = nJ * B
Gam = np.array(list(itertools.product(range(p), repeat=k + 1)), dtype=np.int64)   # B x (k+1)
table = np.array([(1 - (1 - p) ** c) // p for c in range(k + 2)], dtype=np.int64)
assert all((1 - (1 - p) ** c) % p == 0 for c in range(k + 2))
def cycles(J, Jp):
    # returns list of (u, up): the condition is u.gamma + up.gamma' = 0 mod p
    pj = {}; pjp = {}
    for i, (a, b) in enumerate(J): pj[a] = (i, b, +1); pj[b] = (i, a, -1)
    for i, (a, b) in enumerate(Jp): pjp[a] = (i, b, +1); pjp[b] = (i, a, -1)
    seen = set(); out = []
    for v0 in range(N):
        if v0 in seen: continue
        u = [0] * (k + 1); up = [0] * (k + 1); v = v0
        while True:
            seen.add(v); i, w, s = pj[v]; u[i] += s; seen.add(w)
            i2, v2, s2 = pjp[w]; up[i2] += s2; v = v2
            if v == v0: break
        out.append((np.array(u), np.array(up)))
    return out
DT = np.int32 if p ** (2 * M) < 2 ** 31 else np.int64
G = np.zeros((NN, NN), dtype=DT)
for x, J in enumerate(Js):
    for y, Jp in enumerate(Js):
        cnt = np.zeros((B, B), dtype=np.int64)
        for u, up in cycles(J, Jp):
            s = (Gam @ u) % p; sp = (-(Gam @ up)) % p
            cnt += (s[:, None] == sp[None, :])
        G[x*B:(x+1)*B, y*B:(y+1)*B] = table[cnt]
assert all((G[i*B:(i+1)*B] == G[:, i*B:(i+1)*B].T).all() for i in range(nJ))
print(f'(n,p)=({n},{p})  spaces {NN}  Gram built in {time.time()-t0:.1f}s  self-int {G[0,0]}', flush=True)
# rank over a big prime (Gaussian elimination mod P0 on a copy) is skipped: the local Smith form finds it.
def local_smith(HOLD, p, M):
    A = HOLD.pop(); P = p ** M; A %= P; counts = []
    for level in range(M):
        if A.size == 0 or not A.any(): break
        nr, nc = A.shape; ralive = np.ones(nr, bool); calive = np.ones(nc, bool); npiv = 0
        for j in range(nc):
            col = A[:, j]
            cand = np.nonzero(ralive & (col % p != 0))[0]
            if cand.size == 0: continue
            r = int(cand[0]); inv = pow(int(col[r]), -1, P)
            f = ((col.astype(np.int64) * inv) % P).astype(A.dtype); f[r] = 0; f[~ralive] = 0
            prow = A[r, :].copy(); nz = np.nonzero(f)[0]
            for c0 in range(0, nz.size, 256):
                idx = nz[c0:c0+256]
                A[idx, :] = (A[idx, :] - f[idx][:, None] * prow[None, :]) % P
            ralive[r] = False; calive[j] = False; npiv += 1
        A2 = A[np.ix_(ralive, calive)]; del A; A = A2; del A2
        assert all((A[i:i+512] % p == 0).all() for i in range(0, A.shape[0], 512))
        A //= p; P //= p; counts.append(npiv)
        print(f'   level p^{level}: {npiv} divisors   remaining {A.shape}   t={time.time()-t0:.1f}s', flush=True)
    return counts, A
import os
if os.environ.get('PERM'):
    rng = np.random.default_rng(int(os.environ['PERM'])); pr = rng.permutation(NN); pc = rng.permutation(NN)
    G = G[np.ix_(pr, pc)]; print('rows and columns permuted independently, seed', os.environ['PERM'], flush=True)
HOLD = [G]; del G
counts, rest = local_smith(HOLD, p, M)
rank = sum(counts); E = sum(i * c for i, c in enumerate(counts))
print('elementary divisors (p-part):', ' . '.join(f'{p}^{i}:{c}' if i else f'1:{c}' for i, c in enumerate(counts)))
print(f'rank {rank}   remaining block zero mod p^(M-levels): {not rest.any()}   total p-exponent E = {E}')
print('FIN-OK')
