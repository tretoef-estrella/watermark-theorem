import sys; sys.path.insert(0,'.'); import numpy as np
exec(open('w4_route.py').read().split("for m in [5, 7, 11]:")[0])
for m in [5, 7]:
    I = idx(m); G = np.array([[G_entry(m,p,q) for q in I] for p in I], dtype=object)
    F = np.load(f"F{m}.npy").astype(object)
    Bg = [[int(a.dot(G.dot(b))) for b in F] for a in F]
    d = bareiss_det(Bg); print(f"m={m}: det Gram_F = {'+' if d>0 else '-'}m^{vp(d,m)[0]} (rest {vp(d,m)[1]})")
print("FIN-OK")
