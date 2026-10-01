#!/usr/bin/env python3
# Cold reader's own engine. Written from the definitions in the note (§1.2, §3.1), not from engines/.
# usage: cold_delta.py n p [SETS]     n = 2k (dimension), p odd prime, SETS subset of "ABT" (default ABT)
# Computes, straight from the definition:
#   delta_Y = log_p [O~_Y : A_Y]  for Y = A (all primitive chars), B (Hodge = matchable), T = A \ B
#   the Hilbert functions of the point sets [Y] in P^{2k}(F_p) and  sum_j (|[Y]| - h_[Y](j))
#   the identities of Theorem 2.
import sys, itertools, resource
def mem(tag): print(f'   [maxrss {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20:.0f} MB after {tag}]', flush=True)
import numpy as np
n = int(sys.argv[1]); p = int(sys.argv[2]); SETS = sys.argv[3] if len(sys.argv) > 3 else "ABT"
k = n // 2; N = 2 * k + 2; r = N - 1
# largest M with p^M < 3.0e9 (so products fit in int64)
M = 1
while p ** (M + 1) < 3.0e9: M += 1
PM = p ** M

def matchable(a):
    cnt = [0] * p
    for v in a: cnt[v] += 1
    if cnt[0]: return False
    return all(cnt[v] == cnt[p - v] for v in range(1, p))

A_reps, B_reps, T_reps = [], [], []
for tail in itertools.product(range(1, p), repeat=r - 1):
    a = (1,) + tail                      # orbit representative: a_1 = 1
    a0 = (-sum(a)) % p
    if a0 == 0: continue
    full = (a0,) + a
    A_reps.append(a)
    (B_reps if matchable(full) else T_reps).append(a)
alpha, B, t = len(A_reps), len(B_reps), len(T_reps)
kappa = 2 * k * (p - 2) - 1
print(f"n={n} p={p} k={k} N={N} r={r} |G|=p^{r}  alpha={alpha} B={B} t={t} kappa={kappa}  M={M}", flush=True); mem("enumeration")

def eval_matrix(reps):
    # rows: monomials u^e, 0<=e_i<=p-2 (they span Z[G] modulo the N_nu, which vanish on every primitive character)
    es = np.array(list(itertools.product(range(p - 1), repeat=r)), dtype=np.int64)
    R = np.array(reps, dtype=np.int64)
    J = (es @ R.T) % p                    # exponent of zeta at (row, rep)
    rows, cols = J.shape[0], len(reps) * (p - 1)
    Mx = np.zeros((rows, cols), dtype=np.int64)
    ri = np.arange(rows)
    for c in range(len(reps)):
        j = J[:, c]
        ok = j < p - 1
        Mx[ri[ok], c * (p - 1) + j[ok]] = 1
        Mx[ri[~ok], c * (p - 1):(c + 1) * (p - 1)] = PM - 1     # zeta^{p-1} = -(1+...+zeta^{p-2})
    return Mx

def smith_vals(Mx):
    # valuations of the elementary divisors of the Z_p-lattice spanned by the rows (working mod p^M)
    A = Mx; np.remainder(A, PM, out=A)       # in place
    rows, cols = A.shape
    vals = []
    t0 = 0
    for c in range(cols):
        sub = A[t0:, c:]
        v = 0; found = None
        while v < M:                      # block-wise search of the first entry of valuation v (memory-lean)
            qq = p ** (v + 1)
            for r0 in range(0, sub.shape[0], 256):
                mask = (sub[r0:r0 + 256] % qq) != 0
                if mask.any():
                    fl = int(mask.argmax()); found = (r0 + fl // mask.shape[1], fl % mask.shape[1]); break
            if found is not None: break
            v += 1
        if found is None: break
        i, j = int(found[0]) + t0, int(found[1]) + c
        if i != t0: A[[t0, i]] = A[[i, t0]]
        if j != c: A[:, [c, j]] = A[:, [j, c]]
        piv = int(A[t0, c]); unit = piv // (p ** v)
        inv = pow(unit, -1, PM)
        A[t0] = (A[t0] * inv) % PM
        f = (A[t0 + 1:, c] // (p ** v)) % PM
        nzr = np.nonzero(f)[0]
        rowp = A[t0, c:].copy()
        for b0 in range(0, len(nzr), 128):           # chunked: temporaries stay small
            ii = t0 + 1 + nzr[b0:b0 + 128]
            A[ii, c:] = (A[ii, c:] - (f[nzr[b0:b0 + 128], None] * rowp[None, :]) % PM) % PM
        vals.append(v); t0 += 1
        if t0 == rows: break
    return vals

def rank_mod_p(Mx):
    A = Mx % p; rows, cols = A.shape; rk = 0
    for c in range(cols):
        nz = np.nonzero(A[rk:, c])[0]
        if not len(nz): continue
        i = int(nz[0]) + rk
        if i != rk: A[[rk, i]] = A[[i, rk]]
        A[rk] = (A[rk] * pow(int(A[rk, c]), -1, p)) % p
        f = A[:, c].copy(); f[rk] = 0
        nzr = np.nonzero(f)[0]
        if len(nzr): A[nzr] = (A[nzr] - f[nzr, None] * A[rk][None, :]) % p
        rk += 1
        if rk == rows: break
    return rk

def hilbert_points(reps):
    P = np.array(reps, dtype=np.int64); h = []
    j = 0
    while True:
        exps = [e for e in itertools.product(range(j + 1), repeat=r) if sum(e) == j] if j <= 3 else None
        if exps is None:
            exps = []
            def rec(pref, left, pos):
                if pos == r - 1: exps.append(pref + (left,)); return
                for x in range(left + 1): rec(pref + (x,), left - x, pos + 1)
            rec((), j, 0)
        if len(exps) * len(reps) > 6e6: h.append(None); print('   (Hilbert function stopped at degree', j, ': matrix too large)'); break
        E = np.array(exps, dtype=np.int64)
        V = np.ones((len(reps), len(exps)), dtype=np.int64)
        for i in range(r):
            pw = np.ones((len(reps), j + 1), dtype=np.int64)
            for d in range(1, j + 1): pw[:, d] = (pw[:, d - 1] * P[:, i]) % p
            V = (V * pw[:, E[:, i]]) % p
        h.append(rank_mod_p(V))
        if h[-1] == len(reps): break
        j += 1
        if j > 60: break
    return h

res = {}
for name, reps in (("A", A_reps), ("B", B_reps), ("T", T_reps)):
    if name not in SETS or not reps:
        if not reps: res[name] = (0, [])
        continue
    Mx = eval_matrix(reps); mem('eval_matrix')
    vals = smith_vals(Mx); mem('smith')
    full = (len(vals) == Mx.shape[1])
    delta = sum(vals)
    hist = {v: vals.count(v) for v in sorted(set(vals))}
    print(f"delta_{name} = {delta}   (matrix {Mx.shape}, pivots {len(vals)}/{Mx.shape[1]} full={full}, max valuation {max(vals) if vals else 0} < M={M}; histogram {hist})", flush=True)
    h = hilbert_points(reps); mem('hilbert')
    if h[-1] is None: print(f"   Hilbert function of the points [{name}] (incomplete): {h}")
    else:
        cone = sum(len(reps) - x for x in h)
        print(f"   Hilbert function of the points [{name}]: {h}   sum_j(|[Y]|-h(j)) = {cone}   equal to delta: {cone == delta}")
    res[name] = (delta, h)

if "A" in res and "A" in SETS: print("Thm2(i)   2*delta_A - 1 - kappa*alpha =", 2 * res["A"][0] - 1 - kappa * alpha)
if "B" in res and "B" in SETS: print("Thm2(ii)  E = 1 + kappa*B - 2*delta_B =", 1 + kappa * B - 2 * res["B"][0])
if "T" in res and "T" in SETS: print("Thm2(iii) E = kappa*t - 2*delta_T     =", kappa * t - 2 * res["T"][0])
if all(x in SETS for x in "ABT"): print("Thm2(iv)  E = delta_A - delta_B - delta_T =", res["A"][0] - res["B"][0] - res["T"][0])
print("COLD-DONE")
