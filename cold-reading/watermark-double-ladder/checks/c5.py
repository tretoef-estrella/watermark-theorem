# C5: the lines of §3 in P^3(C); two distinct lines meet iff the 4x4 matrix of their four linear equations is singular.
import sys, numpy as np
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from engine import *

for m in [int(a) for a in sys.argv[1:]]:
    eps = np.exp(1j * np.pi / m); zeta = eps ** 2
    E = []
    for (j, a, b) in lines(m):
        r1 = np.zeros(4, complex); r2 = np.zeros(4, complex)
        if j == 0:   # x0 = eps zeta^a x1, x2 = eps zeta^b x3
            r1[0], r1[1] = 1, -eps * zeta**a; r2[2], r2[3] = 1, -eps * zeta**b
        elif j == 1: # x0 = eps zeta^a x2, x1 = eps zeta^b x3
            r1[0], r1[2] = 1, -eps * zeta**a; r2[1], r2[3] = 1, -eps * zeta**b
        else:        # x0 = eps zeta^a x3, x1 = eps zeta^b x2
            r1[0], r1[3] = 1, -eps * zeta**a; r2[1], r2[2] = 1, -eps * zeta**b
        E.append(np.array([r1, r2]))
    E = np.array(E); n = len(E)
    # sanity: lines lie on S_m (two points of each line satisfy the Fermat equation)
    onS = True
    for e in E:
        ns = np.linalg.svd(e)[2][2:].conj()           # basis of the solution plane
        for pt in (ns[0], ns[1], ns[0] + 2 * ns[1]):
            if abs(np.sum(pt ** m)) > 1e-8 * np.sum(abs(pt) ** m): onS = False
    I, J = np.triu_indices(n, 1)
    M = np.concatenate([E[I], E[J]], axis=1)          # (#pairs, 4, 4)
    sv = np.linalg.svd(M, compute_uv=False)[:, -1]
    meet = sv < 1e-9
    gap = (sv[meet].max() if meet.any() else 0, sv[~meet].min())
    G = build_G(m); Gw = build_G(m, shift02=-1)
    agree = np.sum(meet == (G[I, J] == 1)); dis = len(I) - agree
    disw = np.sum(meet != (Gw[I, J] == 1))
    print(f"m={m}: lines on S_m: {onS}; distinct pairs={len(I)}; meeting pairs={meet.sum()}; "
          f"smallest singular value: max over meeting {gap[0]:.1e}, min over non-meeting {gap[1]:.1e}")
    print(f"   agreement with G (off-diagonal): {agree}/{len(I)}, disagreements {dis};  control k+l-1: disagreements {disw} (2m^3={2*m**3})")
    print(f"   diagonal of G = 2-m = {set(np.diag(G))}; with diagonal the paper's count n(n+1)/2 = {n*(n+1)//2}")
