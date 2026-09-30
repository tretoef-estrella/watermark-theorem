# Checks for piece DL2, with the exact definitions of the piece.
import numpy as np, sys
from dl_profile import gram
from dl_steps import rank_mod
def pen(i,k,l,m): return [k,l,(k-l)%m,(k+l)%m][i]
def slots(m): return [(j,i,x) for j in range(3) for i in range(4) for x in range(m)]
def lines(m): return [(j,k,l) for j in range(3) for k in range(m) for l in range(m)]
def shadow(m):
    S=np.zeros((12*m,3*m*m),dtype=np.int64); sl={s:n for n,s in enumerate(slots(m))}
    for c,(j,k,l) in enumerate(lines(m)):
        for i in range(4): S[sl[(j,i,pen(i,k,l,m))],c]=1
    return S
def gam(m):
    sl=slots(m); idx={s:n for n,s in enumerate(sl)}; Gm=np.zeros((12*m,12*m),dtype=np.int64)
    for (j,i,x) in sl:
        for (jj,ii,y) in sl:
            v=0
            if j==jj and i==ii and i in (0,1) and x==y: v=1
            if {(j,i),(jj,ii)}=={(0,2),(1,2)} and x==y: v=1
            if {(j,i),(jj,ii)}=={(1,3),(2,3)} and x==y: v=1
            if (j,i,jj,ii)==(0,3,2,2) and y==(x+1)%m: v=1
            if (j,i,jj,ii)==(2,2,0,3) and x==(y+1)%m: v=1
            Gm[idx[(j,i,x)],idx[(jj,ii,y)]]=v
    return Gm
R6=lambda m:[[lambda x:1,lambda x:-1,lambda x:0,lambda x:0],[lambda x:1,lambda x:0,lambda x:-1,lambda x:0],
    [lambda x:1,lambda x:0,lambda x:0,lambda x:-1],[lambda x:x,lambda x:-x,lambda x:-x,lambda x:0],
    [lambda x:x,lambda x:x,lambda x:0,lambda x:-x],[lambda x:-2*x*x,lambda x:-2*x*x,lambda x:x*x,lambda x:x*x]]
for m in map(int,sys.argv[1:]):
    G=gram(m); S=shadow(m); Gm=gam(m); n=3*m*m
    ok1=np.array_equal(S.T@Gm@S-m*np.eye(n,dtype=np.int64),G); sym=np.array_equal(Gm,Gm.T); inv=np.array_equal(Gm@Gm,np.eye(12*m,dtype=np.int64))
    # relMap for one family: (Fin4 -> ZMod m) -> (Point -> ZMod m)
    T=np.zeros((m*m,4*m),dtype=np.int64)
    for r,(k,l) in enumerate([(k,l) for k in range(m) for l in range(m)]):
        for i in range(4): T[r,i*m+pen(i,k,l,m)]+=1
    kerdim=4*m-rank_mod(T,m)
    vecs=np.array([[f[i](x)%m for i in range(4) for x in range(m)] for f in R6(m)],dtype=np.int64)
    inker=np.all((T@vecs.T)%m==0); indep=rank_mod(vecs,m)
    # quad pairing: f,g quadratic, sum f(x) g(x+e) over Z/m
    import itertools
    bad=0
    for a in itertools.product(range(3),repeat=2):
        for e in (0,1,-1):
            s=sum(pow(x,a[0],m)*pow((x+e)%m,a[1],m) for x in range(m))%m
            bad+= s!=0
    rk=rank_mod(G% m,m)
    print(f"m={m}: G=S^T Gam S - mI {ok1}; Gam sym {sym}; Gam^2=I {inv}; ker relMap dim {kerdim}; R6 in ker {inker}, rank {indep}; quad pairings nonzero {bad}; rank(G mod m) {rk} vs 12(m-3)={12*(m-3)}",flush=True)
