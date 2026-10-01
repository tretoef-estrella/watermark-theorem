# regla296 — recompute with engine 4 every value used by ajuste.py (guards against transcription errors).
import sys; sys.path.insert(0, '.')
from E_estadistica2 import run, E_from
src = open('ajuste.py').read()
ns = {}; exec(src.split('def interp')[0], ns); D = ns['D']
bad = 0; tot = 0
for k in sorted(D):
    for p in sorted(D[k]):
        E = E_from(run(p - 1, 2 * k + 2), k, p); tot += 1
        if E != D[k][p]: bad += 1; print('MISMATCH', k, p, E, D[k][p])
print(f'{tot} cells recomputed, {bad} mismatches'); print('FIN-OK')
