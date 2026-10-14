# C2: dim ker s_{F_m} (Lemma 12). Expect 12 for m = 5,7,11,13 and 11 for m = 3 (Remark 13).
import sys, numpy as np, random
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from engine import *

for m in [int(a) for a in sys.argv[1:]]:
    B = src_basis(m)                       # reductions mod m form an F_m-basis of Src_{F_m}
    S = np.array([s_Z(m, *d) for d in B]) % m
    r = rank_mod_p(S, m)
    print(f"m={m}: dim Src={len(B)} rank s={r} dim ker={len(B)-r} (paper: 12 for m>=5; 11 at m=3); image dim {r} vs 9m-19={9*m-19}")
    # the explicit 12-parameter family of Lemma 12: w_i = c x^2 + a_i x + b_i; check that a_j, b_j exist (separability)
    # and that all nine functions have sum zero mod m.
    random.seed(m)
    good = True; sums0 = True
    for trial in range(20):
        c = random.randrange(m); al = [random.randrange(m) for _ in range(3)]; be = [random.randrange(m) for _ in range(3)]
        e1, e2 = random.randrange(m), random.randrange(m)
        w = [np.array([(c*x*x + al[i]*x + be[i]) % m for x in range(m)]) for i in range(3)]
        Phi = [lambda k, l: -(w[0][(k-l) % m] + w[2][(k+l) % m] + e1),
               lambda k, l: -(w[0][(k-l) % m] + w[1][(k+l) % m] + e2 - e1),
               lambda k, l: -(w[1][(k+l) % m] + w[2][(k-l-1) % m] - e2)]
        for j in range(3):
            for k in range(m):
                for l in range(m):
                    if (Phi[j](k, l) - Phi[j](k, 0) - Phi[j](0, l) + Phi[j](0, 0)) % m: good = False
            a = [Phi[j](k, 0) for k in range(m)]; b = [Phi[j](0, l) - Phi[j](0, 0) for l in range(m)]
            if sum(a) % m or sum(b) % m: sums0 = False
        if any(sum(wi) % m for wi in w): sums0 = False
    print(f"   explicit family: separable={good}, all nine sums zero={sums0}")
