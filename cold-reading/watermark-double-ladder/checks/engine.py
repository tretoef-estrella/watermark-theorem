# engine.py -- Grepy la Filigrana, cold reading WM_DL_HEXAGON_1, 2026-10-14.
# Written from the text of watermark_double_ladder.tex alone (§2, §4, §5). Pure Python + numpy (int64).
import numpy as np

def lines(m):
    return [(j, k, l) for j in range(3) for k in range(m) for l in range(m)]

def idx(m, j, k, l):
    return j * m * m + (k % m) * m + (l % m)

def build_G(m, shift02=+1):
    """G of §2. shift02 is the constant c in the family 0/2 rule k'-l' = k+l+c (paper: +1)."""
    n = 3 * m * m
    G = np.zeros((n, n), dtype=np.int64)
    L = lines(m)
    for a, (j, k, l) in enumerate(L):
        for b, (j2, k2, l2) in enumerate(L):
            if j == j2:
                if (k, l) == (k2, l2):
                    G[a, b] = 2 - m
                elif k == k2 or l == l2:
                    G[a, b] = 1
            elif (j, j2) == (0, 1):
                G[a, b] = int((k - l - k2 + l2) % m == 0)
            elif (j, j2) == (1, 2):
                G[a, b] = int((k + l - k2 - l2) % m == 0)
            elif (j, j2) == (0, 2):
                G[a, b] = int((k2 - l2 - (k + l + shift02)) % m == 0)
    # remaining entries by symmetry (G_qp = G_pq)
    for a, (j, k, l) in enumerate(L):
        for b, (j2, k2, l2) in enumerate(L):
            if (j, j2) in ((1, 0), (2, 1), (2, 0)):
                G[a, b] = G[b, a]
    return G

def pencil(m, t):
    """pi_t(k,l) = k + t l for t in F_m; t = 'inf' gives l."""
    if t == 'inf':
        return lambda k, l: l % m
    return lambda k, l: (k + t * l) % m

def pb(m, j, pi, u):
    v = np.zeros(3 * m * m, dtype=np.int64)
    for k in range(m):
        for l in range(m):
            v[idx(m, j, k, l)] = u[pi(k, l)]
    return v

def N(m, j):
    v = np.zeros(3 * m * m, dtype=np.int64)
    v[j * m * m:(j + 1) * m * m] = 1
    return v

def shift(u, s):
    """u^{+}(x) = u(x+1) for s=+1, u^{-}(x)=u(x-1) for s=-1."""
    m = len(u)
    return np.array([u[(x + s) % m] for x in range(m)], dtype=np.int64)

def Z0_basis(m):
    out = []
    for x in range(1, m):
        u = np.zeros(m, dtype=np.int64); u[x] = 1; u[0] = -1
        out.append(u)
    return out

def s_Z(m, a, b, w, e1, e2):
    """s_Z of a datum (a_j, b_j, w_0..2, eps1, eps2), from the displayed values of Definition 10."""
    v = np.zeros(3 * m * m, dtype=np.int64)
    for k in range(m):
        for l in range(m):
            v[idx(m, 0, k, l)] = a[0][k] + b[0][l] + w[0][(k - l) % m] + w[2][(k + l) % m] + e1
            v[idx(m, 1, k, l)] = a[1][k] + b[1][l] + w[0][(k - l) % m] + w[1][(k + l) % m] + e2 - e1
            v[idx(m, 2, k, l)] = a[2][k] + b[2][l] + w[1][(k + l) % m] + w[2][(k - l - 1) % m] - e2
    return v

def src_basis(m):
    """A Z-basis of Src_Z: one sum-zero function in one of the nine slots, or one epsilon."""
    z = np.zeros(m, dtype=np.int64)
    out = []
    for slot in range(9):
        for u in Z0_basis(m):
            a = [z, z, z]; b = [z, z, z]; w = [z, z, z]
            if slot < 3: a = [u if i == slot else z for i in range(3)]
            elif slot < 6: b = [u if i == slot - 3 else z for i in range(3)]
            else: w = [u if i == slot - 6 else z for i in range(3)]
            out.append((a, b, w, 0, 0))
    out.append(([z]*3, [z]*3, [z]*3, 1, 0))
    out.append(([z]*3, [z]*3, [z]*3, 0, 1))
    return out

def rank_mod_p(M, p):
    """Rank over F_p by Gaussian elimination (exact, int64, p small)."""
    A = np.array(M, dtype=np.int64) % p
    r = 0; rows, cols = A.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i, c] != 0:
                piv = i; break
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, c]), p - 2, p)
        A[r] = (A[r] * inv) % p
        nz = np.nonzero(A[:, c])[0]
        for i in nz:
            if i != r:
                A[i] = (A[i] - A[i, c] * A[r]) % p
        r += 1
        if r == rows: break
    return r
