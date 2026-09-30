# W2 check of the proof route: the F_m-relations among the SAT generators, written in the data
# (a_j, b_j, w_0, w_1, w_2 : F_m -> F_m sum-zero; eps1, eps2), are exactly:
#   w_i(x) = c x^2 + alpha_i x + beta_i (one common c), a_j, b_j determined up to a split (t, -t).
# Test: solve the linear system F1-F3 directly in the function data (dimension of the solution space = 12),
# and check every basis solution has w_i with third difference 0 and a common x^2 coefficient.
import itertools, sys
def solve_dim_and_basis(m):
    # unknowns: a_j(x), b_j(x) (j=0..2), w_i(x) (i=0..2) for x in F_m ; eps1, eps2
    nf = 9*m; N = nf + 2
    def ia(j,x): return j*m + x
    def ib(j,x): return 3*m + j*m + x
    def iw(i,x): return 6*m + i*m + x
    E1, E2 = nf, nf+1
    rows = []
    for k in range(m):
        for l in range(m):
            for j in range(3):
                r = [0]*N
                r[ia(j,k)] += 1; r[ib(j,l)] += 1
                if j == 0: r[iw(0,(k-l)%m)] += 1; r[iw(2,(k+l)%m)] += 1; r[E1] += 1
                if j == 1: r[iw(0,(k-l)%m)] += 1; r[iw(1,(k+l)%m)] += 1; r[E2] += 1; r[E1] -= 1
                if j == 2: r[iw(1,(k+l)%m)] += 1; r[iw(2,(k-l-1)%m)] += 1; r[E2] -= 1
                rows.append([v % m for v in r])
    for f in range(9):   # sum-zero constraints on the nine functions
        r = [0]*N
        for x in range(m): r[f*m + x] = 1
        rows.append(r)
    # nullspace mod m
    M = [row[:] for row in rows]; piv = []; r = 0
    for c in range(N):
        p = next((i for i in range(r, len(M)) if M[i][c] % m), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; inv = pow(M[r][c], m-2, m); M[r] = [(v*inv) % m for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]: f = M[i][c]; M[i] = [(a-f*b) % m for a,b in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(N) if c not in piv]
    basis = []
    for fc in free:
        v = [0]*N; v[fc] = 1
        for i, pc in enumerate(piv): v[pc] = (-M[i][fc]) % m
        basis.append(v)
    ok = True
    for v in basis:
        cs = []
        for i in range(3):
            w = [v[iw(i,x)] for x in range(m)]
            d3 = all((w[(x+3)%m]-3*w[(x+2)%m]+3*w[(x+1)%m]-w[x]) % m == 0 for x in range(m))
            d2 = (w[2]-2*w[1]+w[0]) % m    # = 2c
            ok &= d3; cs.append(d2)
        ok &= (cs[0] == cs[1] == cs[2])
    return len(basis), ok
for m in [5, 7, 11, 13]:
    d, ok = solve_dim_and_basis(m)
    print(f"m={m}: dim of relations = {d} (want 12); every relation has quadratic w's with common leading coeff: {ok}")
d, ok = solve_dim_and_basis(3)
print(f"m=3 (control, degenerate): dim = {d}; property: {ok}")
print("FIN-OK")
