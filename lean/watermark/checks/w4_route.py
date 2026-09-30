# Integer route to |disc V| (Grepy's plan, not the paper's): check its pieces at m = 5, 7, 11.
# pb(j, t, u): pullback of u : ZMod m -> Z along pencil t (t in 0..m-1 or 'inf') on family j.
import sys
sys.path.insert(0, '.')
import numpy as np
exec(open('w1_gram.py').read().split("for m in [5,7,11]")[0])
def bareiss_det(M):
    M = [list(map(int, r)) for r in M]; n = len(M); sign = 1; prev = 1
    for k in range(n-1):
        if M[k][k] == 0:
            sw = next((i for i in range(k+1, n) if M[i][k] != 0), None)
            if sw is None: return 0
            M[k], M[sw] = M[sw], M[k]; sign = -sign
        for i in range(k+1, n):
            for j in range(k+1, n):
                M[i][j] = (M[i][j]*M[k][k] - M[i][k]*M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n-1][n-1]
def vp(x, m):
    x = abs(x); e = 0
    while x and x % m == 0: x //= m; e += 1
    return e, x
for m in [5, 7, 11]:
    I = idx(m); pos = {p: i for i, p in enumerate(I)}; n = len(I)
    G = np.array([[G_entry(m, p, q) for q in I] for p in I], dtype=object)
    def pen(t, k, l): return l % m if t == 'inf' else (k + t*l) % m
    def pb(j, t, u):
        v = np.zeros(n, dtype=object)
        for k in range(m):
            for l in range(m): v[pos[(j, k, l)]] = u[pen(t, k, l)]
        return v
    Z0 = [[(1 if x == i else 0) - (1 if x == 0 else 0) for x in range(m)] for i in range(1, m)]
    ok = True
    for u in Z0:
        us = lambda s: [u[(x - s) % m] for x in range(m)]   # x -> u(x - s)
        for j in range(3):
            for t in ['inf', 0]: ok &= not any(G.dot(pb(j, t, u)))
            for t in range(2, m-1):  # t not in {0, 1, -1}
                ok &= all(G.dot(pb(j, t, u)) == -m * pb(j, t, u))
        # overlap pair formulas: pencil -1 = k - l, pencil 1 = k + l
        ok &= all(G.dot(pb(0, m-1, u)) == -m*pb(0, m-1, u) + m*pb(1, m-1, u))
        ok &= all(G.dot(pb(1, m-1, u)) == -m*pb(1, m-1, u) + m*pb(0, m-1, u))
        ok &= all(G.dot(pb(1, 1, u)) == -m*pb(1, 1, u) + m*pb(2, 1, u))
        ok &= all(G.dot(pb(2, 1, u)) == -m*pb(2, 1, u) + m*pb(1, 1, u))
        # (0,2): family 0 along k+l with u, family 2 along k-l with u(x+1)   [i.e. pb_2^{-1}(x -> u(x+1))]
        ok &= all(G.dot(pb(0, 1, u)) == -m*pb(0, 1, u) + m*pb(2, m-1, us(-1)))
        ok &= all(G.dot(pb(2, m-1, u)) == -m*pb(2, m-1, u) + m*pb(0, 1, us(1)))
    print(f"m={m}: G on pullbacks (axis 0, live non-overlap -m, six overlap formulas): {ok}")
    # L_j index in Z^P: generators pb^t(Z0) for all m+1 pencils, plus the constant 1  (m^2 vectors)
    P = [(k, l) for k in range(m) for l in range(m)]
    gens = []
    for t in list(range(m)) + ['inf']:
        for u in Z0: gens.append([u[pen(t, k, l)] for (k, l) in P])
    gens.append([1]*len(P))
    d = bareiss_det(gens); e, rest = vp(d, m)
    print(f"m={m}: [Z^P : L_j] = m^{e} * {rest}  (predicted m^{(m*m+m+2)//2})")
    if m <= 7:
        # F: live non-overlap blocks, lower member of each overlap pair, N_0 ; B-Gram determinant
        F = []
        for j in range(3):
            for t in range(2, m-1):
                for u in Z0: F.append(pb(j, t, u))
        for (j, t) in [(0, m-1), (1, 1), (0, 1)]:
            for u in Z0: F.append(pb(j, t, u))
        F.append(np.array([1 if p[0] == 0 else 0 for p in I], dtype=object))
        Bg = [[int(a.dot(G.dot(b))) for b in F] for a in F]
        d = bareiss_det(Bg); e, rest = vp(d, m)
        pred = 3*(m-2)*(2*m-1) + 3
        print(f"m={m}: rank F = {len(F)} (3(m-1)(m-2)+1 = {3*(m-1)*(m-2)+1}); |disc B|_F| = m^{e} * {rest}  (predicted m^{pred})")
        np.save(f"F{m}.npy", np.array(F, dtype=np.int64))
print("FIN-OK")
