import numpy as np, sys, sympy
from dl_profile import gram
def feat(m,p,q):
    (j,a,b),(jj,c,d)=p,q
    if j==jj:
        return ('same',j, a==c and b==d, a==c, b==d, (a-b-c+d)%m==0, (a+b-c-d)%m==0)
    return ('cross',j,jj)
def classes(m):
    C=np.load(f"C{m}.npy"); n=C.shape[0]
    L=[(j,a,b) for j in range(3) for a in range(m) for b in range(m)]
    rep={}
    for i in range(n):
        for t in range(n):
            rep.setdefault(int(C[i,t]),(L[i],L[t]))
    return C,L,rep
for m in map(int,sys.argv[1:]):
    G=gram(m); C,L,rep=classes(m); k=C.max()+1
    Bs=[(C==c).astype(np.int64) for c in range(k)]
    A=np.stack([(G@B@G).reshape(-1) for B in Bs],axis=1); rhs=(m*m*G).reshape(-1)
    # independent rows
    Af=A.astype(float); idx=[]; cur=np.zeros((0,k))
    for r in range(A.shape[0]):
        t=np.vstack([cur,Af[r]])
        if np.linalg.matrix_rank(t)>cur.shape[0]: cur=t; idx.append(r)
        if len(idx)==7: break
    As=sympy.Matrix(A[idx].tolist()); bs=sympy.Matrix(rhs[idx].tolist())
    # check full consistency later; general solution
    sol,params=As.gauss_jordan_solve(bs)
    print(f"m={m}: free params {params.shape[0]}")
    # describe classes
    info=[]
    for c in range(k):
        p,q=rep[c]; info.append((c,int(G[L.index(p),L.index(q)]),int(Bs[c].sum()),feat(m,p,q)))
    for c,g,sz,f in info: print(c,g,sz,f)
    print(sol.T)
