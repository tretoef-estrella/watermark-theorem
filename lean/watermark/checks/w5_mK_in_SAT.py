# W5 check: for every basis vector x of K = ker G (from M2, saturated), with m prime:
#  (census) live non-overlap fibre sums of x_j are constant; overlap fibre sums match (with the (0,2) shift);
#  (construction) the datum D built as in the piece is admissible and satMap(D) = m*x exactly.
import sys, re
sys.path.insert(0, '.')
exec(open('w1_gram.py').read().split("for m in [5,7,11]")[0])
for m in [5, 7]:
    I = idx(m); pos = {p: i for i, p in enumerate(I)}; n = len(I)
    txt = open(f"kerG{m}.txt").read()
    rows = [[int(v) for v in re.findall(r'-?\d+', r)] for r in txt.split('}, {')]
    assert all(len(r) == n for r in rows), len(rows)
    def pen(t, k, l): return l % m if t == 'inf' else (k + t*l) % m
    def fib(x, j, t):
        f = [0]*m
        for k in range(m):
            for l in range(m): f[pen(t, k, l)] += x[pos[(j, k, l)]]
        return f
    census = constr = True
    for x in rows:
        aug = [sum(x[pos[(j, k, l)]] for k in range(m) for l in range(m)) for j in range(3)]
        assert sum(aug) == 0 and all(a % m == 0 for a in aug)
        mu = [a // m for a in aug]
        ft = {}
        for j in range(3):
            for t in list(range(m)) + ['inf']:
                f = fib(x, j, t); ft[(j, t)] = [v - mu[j] for v in f]
        for j in range(3):
            for t in range(2, m-1): census &= all(v == 0 for v in ft[(j, t)])
        census &= ft[(0, m-1)] == ft[(1, m-1)] and ft[(1, 1)] == ft[(2, 1)]
        census &= all(ft[(2, m-1)][(v+1) % m] == ft[(0, 1)][v] for v in range(m))
        a = [ft[(j, 0)] for j in range(3)]; b = [ft[(j, 'inf')] for j in range(3)]
        w = [ft[(0, m-1)], ft[(1, 1)], ft[(0, 1)]]; e1, e2 = mu[0], -mu[2]
        ok = all(sum(f) == 0 for f in a + b + w)
        for (j, k, l) in I:
            if j == 0: s = a[0][k] + b[0][l] + w[0][(k-l) % m] + w[2][(k+l) % m] + e1
            if j == 1: s = a[1][k] + b[1][l] + w[0][(k-l) % m] + w[1][(k+l) % m] + (e2 - e1)
            if j == 2: s = a[2][k] + b[2][l] + w[1][(k+l) % m] + w[2][(k-l-1) % m] - e2
            ok &= (s == m * x[pos[(j, k, l)]])
        constr &= ok
    print(f"m={m}: {len(rows)} kernel basis vectors; census holds: {census}; m*x = satMap(D) with D admissible: {constr}")
print("FIN-OK")
