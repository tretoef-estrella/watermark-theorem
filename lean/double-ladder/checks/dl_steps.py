# Step checks for the pencil proof.
# (A) G = S^T Gamma S - m I over Z (12 shadows: per family pencils k, l, k-l, k+l; Gamma pairs axis slots with
#     themselves and the cross slots (0,k-l)<->(1,k-l), (1,k+l)<->(2,k+l), (0,k+l)<->(2,k-l) with shift +1).
# (B) dim W_j = 4m-6 over F_m; W^{perp Gamma} subset W iff m>=7; dim(W cap W^perp)=18 (m>=7), 16 (m=5).
# (C) Y on the W4 pieces: axis -5m, overlap -3m, live -6m, famVec 2m; G on the pieces 0 / pair / -m / mJ.
import numpy as np, sys
from dl_profile import gram
def rank_mod(A,p):
    A=A.copy()%p; r=0; nr,nc=A.shape
    for c in range(nc):
        piv=None
        for i in range(r,nr):
            if A[i,c]%p: piv=i;break
        if piv is None: continue
        A[[r,piv]]=A[[piv,r]]; inv=pow(int(A[r,c]),-1,p); A[r]=(A[r]*inv)%p
        for i in range(nr):
            if i!=r and A[i,c]: A[i]=(A[i]-A[i,c]*A[r])%p
        r+=1
        if r==nr: break
    return r
def shadows(m):
    L=[(j,a,b) for j in range(3) for a in range(m) for b in range(m)]; n=len(L)
    forms=[lambda a,b:a, lambda a,b:b, lambda a,b:a-b, lambda a,b:a+b]
    S=np.zeros((12*m,n),dtype=np.int64)
    for i,(j,a,b) in enumerate(L):
        for s,f in enumerate(forms): S[(4*j+s)*m+f(a,b)%m,i]=1
    Gam=np.zeros((12*m,12*m),dtype=np.int64)
    blk=lambda j,s:(4*j+s)*m
    for j in range(3):
        for s in (0,1):
            for x in range(m): Gam[blk(j,s)+x,blk(j,s)+x]=1
    for x in range(m):
        for (P,Q,sh) in [((0,2),(1,2),0),((1,3),(2,3),0),((0,3),(2,2),1)]:
            u=blk(*P)+x; v=blk(*Q)+(x+sh)%m; Gam[u,v]=1; Gam[v,u]=1
    return L,S,Gam
for m in map(int,sys.argv[1:]):
    G=gram(m); L,S,Gam=shadows(m); n=len(L)
    A_ok=np.array_equal(S.T@Gam@S-m*np.eye(n,dtype=np.int64),G)
    Wj=[rank_mod(S[4*j*m:4*(j+1)*m,j*m*m:(j+1)*m*m],m) for j in range(3)]
    Wbasis=S% m  # columns span W
    # W^perp_Gamma = {y: y^T Gam S = 0}; compute via null space of (Gam S)^T mod m ... use dims:
    # rank of form Gamma on W = rank(S^T Gam S mod m)
    rk=rank_mod(S.T@Gam@S,m); dimW=rank_mod(S,m); rad=dimW-rk
    print(f"m={m}: G=S^T Gam S - mI {A_ok}; dim W_j={Wj} (4m-6={4*m-6}); dim W={dimW}; rank={rk} (12(m-3)={12*(m-3)}); dim(W cap W^perp)={rad}",flush=True)
    # (C) Y on pieces
    from dl_cert import Ymat
    Y=Ymat(m)
    def pb(j,pen,u):
        v=np.zeros(n,dtype=np.int64)
        for i,(jj,a,b) in enumerate(L):
            if jj==j: v[i]=u[(pen(a,b))%m]
        return v
    pens={'k':lambda a,b:a,'l':lambda a,b:b,'k-l':lambda a,b:a-b,'k+l':lambda a,b:a+b,'k+2l':lambda a,b:a+2*b}
    u=np.zeros(m,dtype=np.int64); u[1]=1; u[0]=-1
    res=[]
    for j in range(3):
        for nm,pen in pens.items():
            v=pb(j,pen,u); Yv=Y@v
            c=[t for t in (-6*m,-5*m,-3*m,2*m) if np.array_equal(Yv,t*v)]
            res.append((j,nm,c[0]//m if c else None))
    fv=np.array([1 if l[0]==0 else 0 for l in L]); yf=Y@fv
    print("   Y/m on pb pieces:",res," Y famVec0 = 2m famVec0:",np.array_equal(yf,2*m*fv),flush=True)
