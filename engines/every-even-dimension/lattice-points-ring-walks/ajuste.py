# regla296 — exact interpolation of E_k(p) in x = p - 3. Fit on k+2 primes, test on all the others.
from fractions import Fraction as Fr
D = {
 1: {5:12, 7:48, 11:192, 13:300},
 2: {3:3, 5:303, 7:2043, 11:15603, 13:30303, 17:82743, 19:123363, 23:240603, 29:528063, 31:659403},
 3: {3:24, 5:5596, 7:71368, 11:1149592, 13:2847484, 17:11181628, 19:19229080, 23:47519944, 29:137380540, 31:185343112, 37:405837148},
 4: {3:135, 5:94395, 7:2391135, 11:86168055, 13:277419435, 17:1605935235, 19:3212222055, 23:10180860735, 29:39221628555, 31:57329943855},
 5: {3:663, 5:1536879, 7:79402623, 11:6656548935, 13:28286957823, 17:246709479063, 19:578383119735, 23:2377781289183},
 6: {3:3045, 5:24615997, 7:2637838973, 11:528732016309, 13:3002383849325, 17:40216895824693, 19:111297583266821},
}
for kk,dd in {4: {37: 154586829435, 41: 272452684755}, 5: {29: 12341563501215, 31: 19597140336975, 37: 65478536058543}, 6: {23: 599931260255005, 29: 4240201769855821, 31: 7333547662056749, 37: 30548564682945533, 41: 68833016849915269}, 2: {37: 1180143, 41: 1647303}, 3: {41: 635521372}}.items(): D[kk].update(dd)
D[7]={3: 13464, 5: 390990556, 7: 87926798408, 11: 42993193320472, 13: 329416411600124, 17: 6890121126039868, 19: 22656555107695640, 23: 161771033540979784, 29: 1573150727070413500, 31: 2971131279210941192, 37: 15523603037670237788, 41: 39729911296810953052, 43: 61179452716088718104}
def interp(pts):
    # returns coefficients (low to high) of the polynomial in x through pts = [(x,y)]
    n = len(pts); coef = [Fr(0)] * n
    for i, (xi, yi) in enumerate(pts):
        num = [Fr(1)]; den = Fr(1)
        for j, (xj, _) in enumerate(pts):
            if j == i: continue
            num = [Fr(0)] + num
            for t in range(len(num) - 1): num[t] -= xj * num[t + 1]
            den *= (xi - xj)
        for t in range(n): coef[t] += yi * num[t] / den
    return coef
def ev(c, x): return sum(ci * x ** i for i, ci in enumerate(c))
dfact = lambda n: 1 if n <= 0 else n * dfact(n - 2)
for k, d in D.items():
    ps = sorted(d); deg = k + 1
    if len(ps) < deg + 1:
        print(f'k={k}: only {len(ps)} cells, degree {deg} needs {deg+1}'); continue
    fit = ps[-(deg + 1):]; rest = [p for p in ps if p not in fit]
    c = interp([(Fr(p - 3), Fr(d[p])) for p in fit])
    ok = [(p, ev(c, Fr(p - 3)) == d[p]) for p in rest]
    print(f'k={k}: fitted on p={fit}; tested on {rest}: {ok}')
    print('     E_k = ' + ' + '.join(f'({ci})x^{i}' for i, ci in reversed(list(enumerate(c)))) + f'     leading k(2k+1)!! = {k*dfact(2*k+1)}')
