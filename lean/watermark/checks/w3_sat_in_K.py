# W3 brute force: for every odd m >= 3, G . satMap(D) = 0 for every admissible integer datum D (SAT <= K),
# and satMap is injective on admissible data (rank over Q of the 9m-7 basis images = 9m-7).
# Controls: even m (4, 6) -> SAT not in K; a non-admissible datum (one axis function not sum-zero) -> not in K.
import sys
sys.path.insert(0, '.')
import numpy as np
exec(open('w1_gram.py').read().split("for m in [5,7,11]")[0])   # G_entry, idx only

def sat_vec(m, a, b, w, e1, e2):
    I = idx(m); v = np.zeros(len(I), dtype=np.int64)
    for n_, (j, k, l) in enumerate(I):
        if j == 0: v[n_] = a[0][k] + b[0][l] + w[0][(k-l) % m] + w[2][(k+l) % m] + e1
        if j == 1: v[n_] = a[1][k] + b[1][l] + w[0][(k-l) % m] + w[1][(k+l) % m] + (e2 - e1)
        if j == 2: v[n_] = a[2][k] + b[2][l] + w[1][(k+l) % m] + w[2][(k-l-1) % m] - e2
    return v

def basis(m):
    Z0 = [[(1 if x == i else 0) - (1 if x == 0 else 0) for x in range(m)] for i in range(1, m)]
    zero = [0]*m; out = []
    for slot in range(9):
        for y in Z0:
            f = [[zero]*3 for _ in range(3)]
            f[slot // 3][slot % 3] = y
            out.append(sat_vec(m, f[0], f[1], f[2], 0, 0))
    z3 = [zero]*3
    out.append(sat_vec(m, z3, z3, z3, 1, 0)); out.append(sat_vec(m, z3, z3, z3, 0, 1))
    return out

for m in [3, 4, 5, 6, 7, 9, 11, 15]:
    I = idx(m); G = np.array([[G_entry(m, p, q) for q in I] for p in I], dtype=np.int64)
    B = basis(m)
    inK = all(not np.any(G @ v) for v in B)
    rk = np.linalg.matrix_rank(np.array(B, dtype=float))
    rng = np.random.default_rng(m)
    ok_rand = True
    for _ in range(20):
        def sz():
            y = rng.integers(-9, 10, m); y[0] -= y.sum(); return list(y)
        a = [sz() for _ in range(3)]; b = [sz() for _ in range(3)]; w = [sz() for _ in range(3)]
        ok_rand &= not np.any(G @ sat_vec(m, a, b, w, int(rng.integers(-9, 10)), int(rng.integers(-9, 10))))
    bad = [1] + [0]*(m-1); zero = [0]*m
    ctrl = not np.any(G @ sat_vec(m, [bad, zero, zero], [zero]*3, [zero]*3, 0, 0))
    print(f"m={m}: basis in K: {inK}; 20 random admissible data in K: {ok_rand}; rank_Q={rk} (9m-7={9*m-7}); control non-sum-zero in K: {ctrl}")
print("FIN-OK")
