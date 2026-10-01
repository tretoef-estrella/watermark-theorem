#!/usr/bin/env python3
# Cold reader's engine for Theorem 1 / Remark (ii), ANY degree m >= 3.
# usage: cold_group.py n m H|D
#   H: Y1 = Hodge characters (sum_nu {t a_nu/m} = k+1 for every unit t);  D: Y1 = characters matchable in pairs a_i + a_j = 0.
# Computes the abelian group  Z[G]/(I_{Y1} + I_{Y2}),  Y2 = primitive characters not in Y1,
# as (A_{Y1} x A_{Y2}) / A_Y  (Lemma 3.2 of the note), prime by prime:
#   log_l |Q / l^j Q| = delta_l(L1 + l^j L2) - delta_l(L2),  L1 = A_Y, L2 = A_{Y1} x A_{Y2}, both inside O~ = prod Z[zeta_d].
import sys, itertools, math
import numpy as np
n = int(sys.argv[1]); m = int(sys.argv[2]); mode = sys.argv[3]
k = n // 2; N = 2 * k + 2; r = N - 1
units = [t for t in range(1, m) if math.gcd(t, m) == 1]

def hodge(full):
    for t in units:
        if sum((t * a) % m for a in full) != (k + 1) * m: return False
    return True
def matchable(full):
    cnt = [0] * m
    for v in full: cnt[v] += 1
    for v in range(1, m):
        w = (m - v) % m
        if v == w:
            if cnt[v] % 2: return False
        elif cnt[v] != cnt[w]: return False
    return True
inY1 = hodge if mode == "H" else matchable

def cyclo(d):   # cyclotomic polynomial as list of int coefficients (low degree first)
    from sympy import cyclotomic_poly, Poly, symbols
    x = symbols('x'); c = Poly(cyclotomic_poly(d, x), x).all_coeffs()[::-1]
    return [int(v) for v in c]
red_cache = {}
def red_table(d):   # red_table(d)[j] = coordinates of zeta_d^j in the basis 1..zeta^{phi-1}, j = 0..d-1
    if d in red_cache: return red_cache[d]
    c = cyclo(d); phi = len(c) - 1; tab = []
    v = [0] * phi; v[0] = 1
    for j in range(d):
        tab.append(list(v))
        top = v[-1]; v = [0] + v[:-1]            # multiply by x
        if top: v = [v[i] - top * c[i] for i in range(phi)]   # x^phi = -sum c_i x^i (monic)
    red_cache[d] = tab; return tab

seen = set(); reps = {1: [], 2: []}
for a in itertools.product(range(1, m), repeat=r):
    a0 = (-sum(a)) % m
    if a0 == 0 or a in seen: continue
    full = (a0,) + a
    for t in units: seen.add(tuple((t * x) % m for x in a))
    reps[1 if inY1(full) else 2].append(a)
def order(a): return m // math.gcd(m, math.gcd(*a))
cnt = {i: sum(len(red_table(order(a))[0]) for a in reps[i]) for i in (1, 2)}
print(f"(n,m)=({n},{m}) mode={mode}: orbits Y1={len(reps[1])} Y2={len(reps[2])}; characters |Y1|={cnt[1]} |Y2|={cnt[2]}; rank of the lattice = {cnt[1]+1}", flush=True)

gs = np.array(list(itertools.product(range(m), repeat=r)), dtype=np.int64)
def evalmat(rs):
    cols = []
    for a in rs:
        d = order(a); tab = np.array(red_table(d), dtype=np.int64)        # (d, phi)
        j = (gs @ np.array(a, dtype=np.int64)) % m                          # chi_a(g) = zeta_m^j = zeta_d^{j/(m/d)}
        cols.append(tab[(j // (m // d)) % d])
    return np.concatenate(cols, axis=1) if cols else np.zeros((len(gs), 0), dtype=np.int64)
E1, E2 = evalmat(reps[1]), evalmat(reps[2])
L1 = np.concatenate([E1, E2], axis=1)
L2 = np.concatenate([np.concatenate([E1, np.zeros_like(E2)], axis=1), np.concatenate([np.zeros_like(E1), E2], axis=1)], axis=0)

def delta(Mx, q, Mq):
    QM = q ** Mq
    A = Mx % QM; rows, cols = A.shape; tot = 0; t0 = 0; npiv = 0
    for c in range(cols):
        sub = A[t0:, c:]
        v = 0; found = None
        while v < Mq:
            nz = np.argwhere(sub % (q ** (v + 1)) != 0)
            if len(nz): found = nz[0]; break
            v += 1
        if found is None: break
        i, j = int(found[0]) + t0, int(found[1]) + c
        if i != t0: A[[t0, i]] = A[[i, t0]]
        if j != c: A[:, [c, j]] = A[:, [j, c]]
        unit = int(A[t0, c]) // (q ** v)
        A[t0] = (A[t0] * pow(unit, -1, QM)) % QM
        f = (A[t0 + 1:, c] // (q ** v)) % QM
        nzr = np.nonzero(f)[0]
        if len(nzr): A[t0 + 1 + nzr] = (A[t0 + 1 + nzr] - (f[nzr, None] * A[t0][None, :]) % QM) % QM
        tot += v; t0 += 1; npiv += 1
        if t0 == rows: break
    assert npiv == cols, f"rank deficient mod {q}^{Mq}: {npiv}/{cols}"
    return tot

inv = {}
for q in sorted(set(pf for pf in range(2, m + 1) if m % pf == 0 and all(pf % s for s in range(2, pf)))):
    Mq = 1
    while q ** (Mq + 1) < 3.0e9: Mq += 1
    d1 = delta(L1, q, Mq); d2 = delta(L2, q, Mq)
    print(f"  prime {q}: delta(A_Y) = {d1}, delta(A_Y1 x A_Y2) = {d2}, v_{q}|group| = {d1 - d2}", flush=True)
    e_prev = 0; j = 1
    while True:
        dj = delta(np.concatenate([L1, (q ** j) * L2], axis=0), q, Mq)
        e = dj - d2                               # log_q |Q / q^j Q|
        rj = e - e_prev                           # number of cyclic factors of order >= q^j
        if rj == 0: break
        inv.setdefault(q, []).append(rj); e_prev = e; j += 1
        if e == d1 - d2: break
    fac = inv.get(q, [])
    exact = [fac[i] - (fac[i + 1] if i + 1 < len(fac) else 0) for i in range(len(fac))]
    print(f"  prime {q}: cyclic factors " + " x ".join(f"(Z/{q**(i+1)})^{c}" for i, c in enumerate(exact) if c), flush=True)
print("COLD-DONE")
