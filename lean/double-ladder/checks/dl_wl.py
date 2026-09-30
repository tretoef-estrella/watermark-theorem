# Coherent closure (2-dim WL) of the line configuration; then solve G X G = m^2 G with X in its span.
import numpy as np, sys, sympy
from dl_profile import gram
def wl(m):
    G=gram(m); n=G.shape[0]; fam=np.repeat(np.arange(3),m*m)
    init={}
    C=np.zeros((n,n),dtype=np.int64)
    for i in range(n):
        for j in range(n):
            key=(int(G[i,j]),int(fam[i]),int(fam[j]),i==j)
            C[i,j]=init.setdefault(key,len(init))
    while True:
        k=C.max()+1
        Ms=[(C==c).astype(np.int64) for c in range(k)]
        feats=[C]
        for a in range(k):
            for b in range(k):
                feats.append(Ms[a]@Ms[b])
        st=np.stack(feats,axis=-1).reshape(n*n,-1)
        _,newC=np.unique(st,axis=0,return_inverse=True)
        newC=newC.reshape(n,n)
        if newC.max()+1==k: return G,C,k
        C=newC
for m in map(int,sys.argv[1:]):
    G,C,k=wl(m); n=G.shape[0]
    Bs=[(C==c).astype(np.int64) for c in range(k)]
    # linear system: sum x_c (G B_c G) = m^2 G  -> vectorize
    cols=[ (G@B@G).reshape(-1) for B in Bs]
    Amat=np.stack(cols,axis=1); rhs=(m*m*G).reshape(-1)
    # reduce to independent rows
    Ms=sympy.Matrix(Amat); 
    rk=np.linalg.matrix_rank(Amat.astype(float))
    print(f"m={m}: classes={k} rank of system={rk}",flush=True)
    np.save(f"C{m}.npy",C)
