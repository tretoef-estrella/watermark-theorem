# Double Ladder: elementary-divisor profile of the line Gram G (Lean's Watermark.gram) at prime m,
# and rank of G mod m.  Local Smith form over Z/p^E (valuations 0..E-1, >=E counted as "E+").
import numpy as np, sys
def gram(m):
    L=[(j,a,b) for j in range(3) for a in range(m) for b in range(m)]
    n=len(L); G=np.zeros((n,n),dtype=np.int64)
    def up(p,q):
        (j,k,l),(jj,kk,ll)=p,q
        if j==jj:
            if (k,l)==(kk,ll): return 2-m
            return 1 if (k==kk or l==ll) else 0
        if (j,jj)==(0,1): return 1 if (k-l)%m==(kk-ll)%m else 0
        if (j,jj)==(1,2): return 1 if (k+l)%m==(kk+ll)%m else 0
        if (j,jj)==(0,2): return 1 if (kk-ll)%m==(k+l+1)%m else 0
    for i,p in enumerate(L):
        for t,q in enumerate(L):
            G[i,t]=up(p,q) if p[0]<=q[0] else up(q,p)
    return G
def val(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def profile(G,p,E):
    P=p**E; A=G%P; n=A.shape[0]; prof={}
    r=0
    rows=list(range(n)); 
    A=A.copy()
    for step in range(n):
        sub=A[step:,step:]
        if sub.size==0: break
        # find entry of minimal valuation
        best=None
        for v in range(E):
            mask=(sub % p**(v+1))!=0
            if mask.any():
                i,j=np.argwhere(mask)[0]; best=(v,i+step,j+step); break
        if best is None:
            prof['>=%d'%E]=prof.get('>=%d'%E,0)+(n-step); break
        v,i,j=best; prof[v]=prof.get(v,0)+1
        A[[step,i]]=A[[i,step]]; A[:,[step,j]]=A[:,[j,step]]
        piv=int(A[step,step]); u=piv//p**v; uinv=pow(u,-1,P)
        # eliminate column and row: entries below/right divisible by p^v
        col=A[step+1:,step].copy(); 
        f=( (col//p**v) * uinv ) % P
        A[step+1:,:]=(A[step+1:,:]-np.outer(f,A[step,:]))%P
        row=A[step,step+1:].copy()
        g=((row//p**v)*uinv)%P
        A[:,step+1:]=(A[:,step+1:]-np.outer(A[:,step],g))%P
    return prof
def rank_mod(G,p):
    return sum(c for v,c in profile(G,p,1).items() if v==0)
if __name__=="__main__":
 for m in map(int,sys.argv[1:]):
     G=gram(m); E=4
     pr=profile(G,m,E)
     rk=pr.get(0,0)
     b=pr.get(2,0); a=pr.get(1,0)
     print(f"m={m}: n={3*m*m} profile(val:count)={dict(sorted(pr.items(),key=lambda t:str(t[0])))}  rank mod m={rk} (12(m-3)={12*(m-3)})  a={a} (3m^2-24m+59={3*m*m-24*m+59})  b={b} (3m-16={3*m-16})  kernel-part expected 9m-7={9*m-7}",flush=True)
