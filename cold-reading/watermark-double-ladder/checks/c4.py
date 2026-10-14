# C4 (numpy part): GYG = 6m^2 G (control 6m G), G = S^T Gamma S - mI (control: opposite shift), rank(G mod m).
import sys, numpy as np
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from engine import *

for m in [int(a) for a in sys.argv[1:]]:
    G = build_G(m); n = 3 * m * m
    L = lines(m)
    def Pmat(P):
        M = np.zeros((n, n), dtype=np.int64)
        for a, (j, k, l) in enumerate(L):
            for b, (j2, k2, l2) in enumerate(L):
                if j == j2 and P(k, l) == P(k2, l2): M[a, b] = 1
        return M
    P0, Pinf, Pm, Pp = pencil(m, 0), pencil(m, 'inf'), pencil(m, -1), pencil(m, 1)
    Y = Pmat(P0) + Pmat(Pinf) + 3 * Pmat(Pm) + 3 * Pmat(Pp) - 6 * m * np.eye(n, dtype=np.int64)
    GYG = G @ Y @ G
    print(f"m={m}: GYG == 6m^2 G: {np.array_equal(GYG, 6*m*m*G)};  control GYG == 6m G: {np.array_equal(GYG, 6*m*G)}")
    # minimal polynomial check: G(G+m)(G+2m)(G-3m) == 0 and no proper factor kills G
    I = np.eye(n, dtype=np.int64)
    f = lambda fac: np.linalg.multi_dot([G - c * I for c in fac]) if len(fac) > 1 else G - fac[0] * I
    full = [0, -m, -2*m, 3*m]
    print("   min poly x(x+m)(x+2m)(x-3m) kills G:", not f(full).any(),
          "; each 3-factor product kills G:", [not f([c for c in full if c != d]).any() for d in full])
    # shadows: slots (j, pencil) for pencil in [pi0, pi_inf, pi_-1, pi_1]
    pens = [P0, Pinf, Pm, Pp]
    slot = lambda j, s: (j * 4 + s) * m
    S = np.zeros((12 * m, n), dtype=np.int64)
    for a, (j, k, l) in enumerate(L):
        for s, P in enumerate(pens):
            S[slot(j, s) + P(k, l), a] = 1
    def Gamma(sh):
        Gm = np.zeros((12 * m, 12 * m), dtype=np.int64)
        for j in range(3):
            for s in (0, 1):
                for v in range(m): Gm[slot(j, s) + v, slot(j, s) + v] = 1
        pairs = [((0, 2), (1, 2), 0), ((1, 3), (2, 3), 0), ((0, 3), (2, 2), sh)]
        for (j1, s1), (j2, s2), d in pairs:
            for v in range(m):
                Gm[slot(j1, s1) + v, slot(j2, s2) + (v + d) % m] = 1
                Gm[slot(j2, s2) + (v + d) % m, slot(j1, s1) + v] = 1
        return Gm
    Gam = Gamma(+1)
    print(f"   Gamma^2 == I: {np.array_equal(Gam @ Gam, np.eye(12*m, dtype=np.int64))};  G == S^T Gamma S - mI: {np.array_equal(G, S.T @ Gam @ S - m*np.eye(n, dtype=np.int64))};"
          f"  control (shift -1): {np.array_equal(G, S.T @ Gamma(-1) @ S - m*np.eye(n, dtype=np.int64))}")
    rW = rank_mod_p(S, m)
    rG = rank_mod_p(G, m)
    print(f"   dim W = rank S mod m = {rW} (paper 12m-18={12*m-18});  rank(G mod m) = {rG} (paper: {26 if m==5 else 12*(m-3)})")
