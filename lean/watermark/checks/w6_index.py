# W6 check: [A : F + SAT] = m^{3(m^2+m+2)/2} (so F + SAT = L = ⊕_j L_j, as both contain... and L has that index),
# and F ∩ K = 0 (F + SAT has full rank 3m^2 with rank F + rank SAT = 3m^2).
import sys; sys.path.insert(0, '.')
import numpy as np
exec(open('w4_route.py').read().split("for m in [5, 7, 11]:")[0])
for m in [5, 7]:
    I = idx(m); pos = {p: i for i, p in enumerate(I)}; n = len(I)
    F = np.load(f"F{m}.npy").tolist()
    Z0 = [[(1 if x == i else 0) - (1 if x == 0 else 0) for x in range(m)] for i in range(1, m)]
    def sv(a, b, w, e1, e2):
        v = [0]*n
        for (j, k, l) in I:
            if j == 0: v[pos[(j,k,l)]] = a[0][k]+b[0][l]+w[0][(k-l)%m]+w[2][(k+l)%m]+e1
            if j == 1: v[pos[(j,k,l)]] = a[1][k]+b[1][l]+w[0][(k-l)%m]+w[1][(k+l)%m]+e2-e1
            if j == 2: v[pos[(j,k,l)]] = a[2][k]+b[2][l]+w[1][(k+l)%m]+w[2][(k-l-1)%m]-e2
        return v
    z = [0]*m; S = []
    for slot in range(9):
        for y in Z0:
            f = [[z]*3 for _ in range(3)]; f[slot//3][slot%3] = y; S.append(sv(f[0], f[1], f[2], 0, 0))
    S.append(sv([z]*3, [z]*3, [z]*3, 1, 0)); S.append(sv([z]*3, [z]*3, [z]*3, 0, 1))
    M = F + S
    d = bareiss_det(M); e, rest = vp(d, m)
    print(f"m={m}: #F={len(F)} #SAT={len(S)} total={len(M)} (3m^2={n}); [A : F+SAT] = m^{e} * {rest}  (predicted m^{3*(m*m+m+2)//2})")
print("FIN-OK")
