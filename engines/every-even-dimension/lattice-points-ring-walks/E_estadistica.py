# regla296 — E_k(p) from the fibre-rank statistic on closed walks (engine of corpus4/regla_oro_gordo_2026-10-01/rango_par.py),
# which reproduces the Hilbert function a(i) of Q[x_0..x_{2k+1}]/(e_odd, x_i^{p-1}) (16/16 even-box cells against Macaulay2).
#   E = 2 sum_{j=0}^{m} h(j) - B + 1,  h(j) = sum_{s>=0} a(j - s(p-1)),  m = k(p-2)-1,  B = Q_k(p)/(p-1).
import sys, re, glob, os
from functools import lru_cache
sys.setrecursionlimit(100000)
def run(q, n):
    m = q // 2; S = []
    for i in range(m):
        for s in (1, -1):
            v = [0] * m; v[i] = s; S.append(tuple(v))
    sub = lambda b, c: tuple(x - y for x, y in zip(b, c))
    @lru_cache(None)
    def Nw(j, b):
        if j == 0: return 1 if all(x == 0 for x in b) else 0
        if sum(abs(x) for x in b) > j: return 0
        return sum(Nw(j - 1, sub(b, c)) for c in S)
    @lru_cache(None)
    def F(j, b):
        if j == 0: return (1,) if all(x == 0 for x in b) else ()
        ch = sorted([(Nw(j - 1, sub(b, c)), kk, sub(b, c)) for kk, c in enumerate(S)], key=lambda x: (-x[0], x[1]))
        poly = {}
        for r, (cnt, kk, bb) in enumerate(ch):
            if cnt == 0: continue
            for d, a in enumerate(F(j - 1, bb)): poly[d + r] = poly.get(d + r, 0) + a
        L = max(poly) + 1 if poly else 0
        return tuple(poly.get(d, 0) for d in range(L))
    return list(F(n, tuple([0] * m)))
def E_from(a, k, p):
    q1 = p - 1; m = k * (p - 2) - 1; B = sum(a) // q1
    h = lambda j: sum(a[j - s * q1] for s in range(j // q1 + 1) if 0 <= j - s * q1 < len(a))
    return 2 * sum(h(j) for j in range(m + 1)) - B + 1, B
if __name__ == '__main__':
    here = os.path.dirname(os.path.abspath(__file__))
    cells = [tuple(map(int, c.split(','))) for c in sys.argv[1:]]
    for k, p in cells:
        a = run(p - 1, 2 * k + 2); E, B = E_from(a, k, p)
        chk = ''
        fn = os.path.join(here, f'ta_{k}_{p}.log')
        if os.path.exists(fn):
            mm = re.search(r' a = \[(.*)\]', open(fn).read())
            if mm: chk = '   a == Macaulay2: ' + str([int(x) for x in mm.group(1).split(',')] == a)
        print(f'(k,p)=({k},{p})  Q={sum(a)}  top degree {len(a)-1} (expected {(k+1)*(p-2)})  a(top)={a[-1]}  E = {E}{chk}', flush=True)
    print('FIN-OK')
