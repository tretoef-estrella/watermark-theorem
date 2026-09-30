import numpy as np, sys, sympy
from dl_profile import gram
def typ(m,p,q):
    (j,a,b),(jj,c,d)=p,q
    if j==jj:
        if (a,b)==(c,d): return 'diag'
        if a==c or b==d: return 'axis'
        if (a-b-c+d)%m==0 or (a+b-c-d)%m==0: return 'crossdir'
        return 'gen'
    return 'inc' if gram_entry(m,p,q)==1 else 'non'
def gram_entry(m,p,q):
    (j,k,l),(jj,kk,ll)=(p,q) if p[0]<=q[0] else (q,p)
    if (j,jj)==(0,1): return 1 if (k-l)%m==(kk-ll)%m else 0
    if (j,jj)==(1,2): return 1 if (k+l)%m==(kk+ll)%m else 0
    if (j,jj)==(0,2): return 1 if (kk-ll)%m==(k+l+1)%m else 0
T=['diag','axis','crossdir','gen','inc','non']
for m in map(int,sys.argv[1:]):
    G=gram(m); L=[(j,a,b) for j in range(3) for a in range(m) for b in range(m)]; n=len(L)
    Bs={t:np.zeros((n,n),dtype=np.int64) for t in T}
    for i,p in enumerate(L):
        for s,q in enumerate(L): Bs[typ(m,p,q)][i,s]=1
    A=np.stack([(G@Bs[t]@G).reshape(-1) for t in T],axis=1); rhs=(m*m*G).reshape(-1)
    rows=np.unique(np.concatenate([A,rhs[:,None]],axis=1),axis=0)
    As=sympy.Matrix(rows[:,:-1].tolist()); bs=sympy.Matrix(rows[:,-1].tolist())
    try:
        sol,par=As.gauss_jordan_solve(bs); print(f"m={m}: solution {dict(zip(T,list(sol)))} params {list(par)}")
    except ValueError as e: print(f"m={m}: NO symmetric solution")
