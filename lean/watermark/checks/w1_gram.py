# W1 brute force: the Watermark Gram (paper §2) — symmetry, G·N_j = m·1, R.1, and export for M2 (R.2).
import sys, itertools
def G_entry(m, p, q):
    (j,k,l),(jj,kk,ll) = p, q
    if j == jj:
        if (k,l) == (kk,ll): return 2 - m
        return 1 if (k == kk or l == ll) else 0
    a, b = (p, q) if j < jj else (q, p)          # a in the lower family
    (ja,ka,la),(jb,kb,lb) = a, b
    if (ja,jb) == (0,1): return 1 if (ka-la) % m == (kb-lb) % m else 0
    if (ja,jb) == (1,2): return 1 if (ka+la) % m == (kb+lb) % m else 0
    if (ja,jb) == (0,2): return 1 if (kb-lb) % m == (ka+la+1) % m else 0
def idx(m): return [(j,k,l) for j in range(3) for k in range(m) for l in range(m)]
for m in [5,7,11]:
    I = idx(m); n = len(I)
    G = [[G_entry(m,p,q) for q in I] for p in I]
    sym = all(G[a][b] == G[b][a] for a in range(n) for b in range(n))
    GN = all(sum(G[a][b] for b in range(n) if I[b][0]==j) == m for a in range(n) for j in range(3))
    # R.1: on one family, sum over the m+1 pencils of E_L equals m*I + J
    pts = [(k,l) for k in range(m) for l in range(m)]
    pencils = [lambda k,l,t=t: (k+t*l) % m for t in range(m)] + [lambda k,l: l % m]
    ok_R1 = True
    for p in pts:
        for q in pts:
            s = sum(1 for L in pencils if L(*p) == L(*q))
            want = m*(p==q) + 1
            ok_R1 &= (s == want)
    print(f"m={m} n={n} symmetric={sym} G.N_j=m.1:{GN} R.1:{ok_R1}")
    if m in (5,7):
        with open(f"/Users/rafa/Desktop/ARBOLYAML/ARISTOTLE_LEAN/WATERMARK/checks/G{m}.m2","w") as f:
            f.write("G = matrix{" + ",".join("{"+",".join(map(str,r))+"}" for r in G) + "};\n")
print("FIN-OK")
