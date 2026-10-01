# regla296 — same as E_estadistica.py, with the states reduced by the hyperoctahedral symmetry
# (the polynomial F(j,b) only depends on the sorted absolute values of b: tied steps have symmetric children).
# Calibrated against E_estadistica.py on every cell both can reach.
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
def run(q, n):
    m = q // 2
    canon = lambda b: tuple(sorted((abs(x) for x in b), reverse=True))
    @lru_cache(None)
    def Nw(j, b):            # b canonical
        if j == 0: return 1 if b[0] == 0 else 0
        if sum(b) > j or (sum(b) - j) % 2: return 0
        tot = 0
        for i in range(m):
            for s in (1, -1):
                c = list(b); c[i] += s; tot += Nw(j - 1, canon(c))
        return tot
    @lru_cache(None)
    def F(j, b):
        if j == 0: return (1,) if b[0] == 0 else ()
        ch = []
        for i in range(m):
            for s in (1, -1):
                c = list(b); c[i] -= s; cc = canon(c); ch.append((Nw(j - 1, cc), cc))
        ch.sort(key=lambda t: -t[0])
        poly = {}
        for r, (cnt, cc) in enumerate(ch):
            if cnt == 0: continue
            for d, a in enumerate(F(j - 1, cc)): poly[d + r] = poly.get(d + r, 0) + a
        L = max(poly) + 1 if poly else 0
        return tuple(poly.get(d, 0) for d in range(L))
    return list(F(n, tuple([0] * m)))
def E_from(a, k, p):
    q1 = p - 1; m = k * (p - 2) - 1; B = sum(a) // q1
    h = lambda j: sum(a[j - s * q1] for s in range(j // q1 + 1) if 0 <= j - s * q1 < len(a))
    return 2 * sum(h(j) for j in range(m + 1)) - B + 1
if __name__ == '__main__':
    for c in sys.argv[1:]:
        k, p = map(int, c.split(',')); a = run(p - 1, 2 * k + 2)
        print(f'(k,p)=({k},{p})  Q={sum(a)}  top degree {len(a)-1}  a(top)={a[-1]}  E = {E_from(a, k, p)}', flush=True)
    print('FIN-OK')
