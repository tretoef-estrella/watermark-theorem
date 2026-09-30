# W2 brute force: the SAT generators (paper §7) lie in K = ker G; which shift s for the (0,2) overlap;
# rank over Q = 9m-7; rank mod m = 9m-19 (Lemma C, paper §9); kernel of the mod-m map = 12.
# Negative controls: wrong shift not in K; wrong pencil pairing not in K; m=3 gives a different count.
import sys
sys.path.insert(0,'.')
from w1_gram import G_entry, idx
import numpy as np
from fractions import Fraction

def rank_mod(M, p):
    M = [list(r) for r in M]; r = 0; rows = len(M); cols = len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] % p), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p-2, p)
        M[r] = [(x*inv) % p for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % p:
                f = M[i][c]; M[i] = [(a - f*b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r

def rank_Q(M):
    return int(np.linalg.matrix_rank(np.array(M, dtype=float)))

def gens(m, s, pairs):
    I = idx(m); pos = {p:i for i,p in enumerate(I)}; n = len(I)
    Z0 = [[(1 if x == i else 0) - (1 if x == 0 else 0) for x in range(m)] for i in range(1, m)]
    out = []
    def vec(parts):
        v = [0]*n
        for (j, f) in parts:
            for k in range(m):
                for l in range(m):
                    v[pos[(j,k,l)]] += f(k, l)
        return v
    for j in range(3):
        for y in Z0: out.append(vec([(j, lambda k,l,y=y: y[k])]))
        for y in Z0: out.append(vec([(j, lambda k,l,y=y: y[l])]))
    for (ja, fa, jb, fb) in pairs:
        for y in Z0: out.append(vec([(ja, lambda k,l,y=y,fa=fa: y[fa(k,l) % m]), (jb, lambda k,l,y=y,fb=fb: y[fb(k,l) % m])]))
    N = [[1 if p[0] == j else 0 for p in I] for j in range(3)]
    out.append([a-b for a,b in zip(N[0],N[1])]); out.append([a-b for a,b in zip(N[1],N[2])])
    return out

def in_K(m, vs):
    I = idx(m); G = np.array([[G_entry(m,p,q) for q in I] for p in I], dtype=np.int64)
    return all(not np.any(G @ np.array(v, dtype=np.int64)) for v in vs)

for m in [3, 5, 7, 11]:
    good = None
    for s in range(m):
        pairs = [(0, lambda k,l: k-l, 1, lambda k,l: k-l),
                 (1, lambda k,l: k+l, 2, lambda k,l: k+l),
                 (0, lambda k,l: k+l, 2, lambda k,l,s=s: k-l+s)]
        g = gens(m, s, pairs)
        ok = in_K(m, g)
        print(f"m={m} shift s={s}: SAT in K: {ok}")
        if ok: good = (s, g)
    if good:
        s, g = good
        rq = rank_Q(g) if m <= 7 else rank_mod(g, 1000003)
        rm = rank_mod(g, m)
        print(f"m={m} s={s}: #gens={len(g)} (9m-7={9*m-7}) rank_Q={rq} rank_mod_m={rm} (9m-19={9*m-19}) kernel_mod_m={len(g)-rm}")
    # negative control: swap the pencils of the (0,2) pair
    bad = [(0, lambda k,l: k-l, 1, lambda k,l: k-l), (1, lambda k,l: k+l, 2, lambda k,l: k+l),
           (0, lambda k,l: k-l, 2, lambda k,l: k+l)]
    print(f"m={m} control (0,2) with pencils swapped: in K: {in_K(m, gens(m, 0, bad))}")
print("FIN-OK")
