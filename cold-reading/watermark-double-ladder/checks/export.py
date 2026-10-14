# export.py: writes, for each m given, checks/data_m{m}.gp with the matrices built by engine.py from the text:
# G, SATgens (rows = s_Z of a Z-basis of Src_Z), Fb (columns = the basis c of F of §8: N_0 and pb(delta_x - delta_0)),
# Lgens (rows = the m^2 generators of L_fam of Lemma 20).
import sys, numpy as np
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from engine import *

def gpmat(name, M):
    rows = [",".join(str(int(x)) for x in r) for r in M]
    return f"{name}=[" + ";".join(rows) + "];\n"

out_dir = sys.argv[0].rsplit('/', 1)[0]
for m in [int(a) for a in sys.argv[1:]]:
    G = build_G(m)
    SAT = np.array([s_Z(m, *d) for d in src_basis(m)])
    live = list(range(2, m - 1))
    blocks = [(j, pencil(m, t)) for j in range(3) for t in live] + [(0, pencil(m, -1)), (1, pencil(m, 1)), (0, pencil(m, 1))]
    F = [N(m, 0)]
    for (j, P) in blocks:
        for u in Z0_basis(m):
            F.append(pb(m, j, P, u))
    F = np.array(F)
    # L_fam generators on P (index k*m+l): (delta_x - delta_0) o pi for all m+1 pencils, x != 0, and the constant 1
    Lg = []
    for t in list(range(m)) + ['inf']:
        P = pencil(m, t)
        for u in Z0_basis(m):
            Lg.append([u[P(k, l)] for k in range(m) for l in range(m)])
    Lg.append([1] * (m * m))
    with open(f"{out_dir}/data_m{m}.gp", "w") as f:
        f.write(f"m={m};\n" + gpmat("G", G) + gpmat("SATg", SAT) + gpmat("Fr", F) + gpmat("Lg", np.array(Lg)))
    print(f"m={m}: G {G.shape}, SAT gens {SAT.shape}, F basis {F.shape} (expect rank 3(m-2)(m-1)+1={3*(m-2)*(m-1)+1}), L_fam gens {len(Lg)}")
