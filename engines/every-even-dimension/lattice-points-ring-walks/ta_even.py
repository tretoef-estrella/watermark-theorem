# regla296 — Hilbert function a(i) of the Theorem-A ring with the EVEN box p-1:
#     A = F_p[x_0..x_{N-1}] / (e_1, e_3, ..., e_{2k+1}, x_i^{p-1}),  N = 2k+2,
# computed with Macaulay2 (an algebra engine independent of the point engine), and the exponent
#     E = 2 sum_{j<m} h(j) + h(m) - a(T') + 1,   h(j) = sum_{s>=0} a(j - s(p-1)),  m = k(p-2)-1,  T' = (k+1)(p-2).
# Usage: python3 ta_even.py k p [char]     (char defaults to p; char = 0 means QQ)
import sys, subprocess, re
k, p = int(sys.argv[1]), int(sys.argv[2]); ch = int(sys.argv[3]) if len(sys.argv) > 3 else p
N = 2 * k + 2; q1 = p - 1; T1 = (k + 1) * (p - 2); m = k * (p - 2) - 1
kk = 'QQ' if ch == 0 else f'ZZ/{ch}'
code = f'''
clN = {N}; clR = {kk}[clx_0..clx_(clN-1)];
clE = j -> sum(subsets(clN, j), s -> product(s, i -> clx_i));
clI = ideal(apply(toList(0..{k}), i -> clE(2*i+1))) + ideal(apply(clN, i -> clx_i^{q1}));
clA = clR/clI;
print("HF " | toString(apply({T1 + 2}, d -> hilbertFunction(d, clA))));
print("DIM " | toString(degree clA));
'''
out = subprocess.run(['/opt/homebrew/bin/M2', '--silent', '-q', '-e', code + 'exit 0'], capture_output=True, text=True).stdout
a = [int(x) for x in re.search(r'HF \{(.*)\}', out).group(1).split(',')]
dim = int(re.search(r'DIM (\d+)', out).group(1))
h = lambda j: sum(a[j - s * q1] for s in range(j // q1 + 1) if 0 <= j - s * q1 < len(a))
E = 2 * sum(h(j) for j in range(m)) + h(m) - a[T1] + 1
print(f'(k,p)=({k},{p}) char {ch}:  dim A = {dim}   top degree {T1}: a(T\') = {a[T1]}, a(T\'+1) = {a[T1+1]}')
print(' a =', a[:T1 + 1])
print(f'RESULT TA (n,p)=({2*k},{p}) char {ch}: E = {E}')
print('FIN-OK')
