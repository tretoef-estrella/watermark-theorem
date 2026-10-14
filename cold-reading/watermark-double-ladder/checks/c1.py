# C1: G symmetric, Lemma 4, Lemma 9 (all six overlap formulas + axis + live) on a basis of Z_0, controls, Lemma 11.
import sys, numpy as np
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from engine import *

for m in [int(a) for a in sys.argv[1:]]:
    G = build_G(m)
    n = 3 * m * m
    print(f"m={m} n={n} symmetric={np.array_equal(G, G.T)} diag={set(np.diag(G))}")
    one = sum(N(m, j) for j in range(3))
    print("  Lemma4 GN_j=m1:", all(np.array_equal(G @ N(m, j), m * one) for j in range(3)),
          " G1=3m1:", np.array_equal(G @ one, 3 * m * one))
    P0, Pinf, Pm, Pp = pencil(m, 0), pencil(m, 'inf'), pencil(m, -1), pencil(m, 1)
    ok = {k: True for k in ['a', 'b', 'c1', 'c2', 'c3', 'c4', 'c5', 'c6', 'ctrl5', 'ctrl6']}
    for u in Z0_basis(m):
        um, up = shift(u, -1), shift(u, +1)
        for j in range(3):
            ok['a'] &= not (G @ pb(m, j, P0, u)).any() and not (G @ pb(m, j, Pinf, u)).any()
            for t in range(2, m - 1):  # live: t not in {0,1,-1}
                v = pb(m, j, pencil(m, t), u)
                ok['b'] &= np.array_equal(G @ v, -m * v)
        f = lambda j, P, uu: pb(m, j, P, uu)
        ok['c1'] &= np.array_equal(G @ f(0, Pm, u), -m * f(0, Pm, u) + m * f(1, Pm, u))
        ok['c2'] &= np.array_equal(G @ f(1, Pm, u), -m * f(1, Pm, u) + m * f(0, Pm, u))
        ok['c3'] &= np.array_equal(G @ f(1, Pp, u), -m * f(1, Pp, u) + m * f(2, Pp, u))
        ok['c4'] &= np.array_equal(G @ f(2, Pp, u), -m * f(2, Pp, u) + m * f(1, Pp, u))
        ok['c5'] &= np.array_equal(G @ f(0, Pp, u), -m * f(0, Pp, u) + m * f(2, Pm, um))
        ok['c6'] &= np.array_equal(G @ f(2, Pm, u), -m * f(2, Pm, u) + m * f(0, Pp, up))
        # controls: the opposite shift must FAIL
        ok['ctrl5'] &= np.array_equal(G @ f(0, Pp, u), -m * f(0, Pp, u) + m * f(2, Pm, up))
        ok['ctrl6'] &= np.array_equal(G @ f(2, Pm, u), -m * f(2, Pm, u) + m * f(0, Pp, um))
    print("  Lemma9:", {k: bool(v) for k, v in ok.items()}, "(ctrl5/ctrl6 must be False)")
    # control 2: G built with k+l-1 in the 0/2 rule fails formula (5) as printed
    Gw = build_G(m, shift02=-1)
    u = Z0_basis(m)[0]
    print("  ctrl G(k+l-1) satisfies (c5):", np.array_equal(Gw @ pb(m, 0, Pp, u), -m * pb(m, 0, Pp, u) + m * pb(m, 2, Pm, shift(u, -1))))
    # Lemma 11: SAT subset K on a Z-basis of Src_Z
    B = src_basis(m)
    S = np.array([s_Z(m, *d) for d in B])
    print(f"  Lemma11: #basis of Src_Z={len(B)} (9m-7={9*m-7}); G*s=0 for all: {not (G @ S.T).any()}")
    # control: a non-admissible datum (w_0 = delta_0, not sum zero) is NOT in K
    z = np.zeros(m, dtype=np.int64); d = z.copy(); d[0] = 1
    print("  ctrl non-admissible datum in K:", not (G @ s_Z(m, [z]*3, [z]*3, [d, z, z], 0, 0)).any())
    # control: wrong shift in family 2 (w_2(k-l+1)) breaks SAT in K
    sw = s_Z(m, [z]*3, [z]*3, [z, z, Z0_basis(m)[0]], 0, 0)
    w2 = Z0_basis(m)[0]
    for k in range(m):
        for l in range(m):
            sw[idx(m, 2, k, l)] = w2[(k - l + 1) % m]
    print("  ctrl w2(k-l+1) in K:", not (G @ sw).any())
