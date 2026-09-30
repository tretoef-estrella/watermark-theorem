# Is the Lean matrix `Watermark.gram m` the intersection matrix of the 3m^2 lines of the
# complex Fermat surface x0^m + x1^m + x2^m + x3^m = 0 ?  Expected output: "MATCH" for every m.
# Lines (eps = exp(pi i/m), zeta = exp(2 pi i/m), so eps^m = -1):
#  family 0: x0 = eps*zeta^a x1, x2 = eps*zeta^b x3   -> Lean index (0,(a,b))
#  family 1: x0 = eps*zeta^c x2, x1 = eps*zeta^d x3   -> Lean index (1,(c,d))
#  family 2: x0 = eps*zeta^e x3, x1 = eps*zeta^f x2   -> Lean index (2,(e,f))
# Two distinct lines meet (intersection number 1) iff their 4 linear equations have a
# nonzero common solution; a line has self-intersection 2 - m (adjunction, K = (m-4)H).
import numpy as np, sys
def lean_upper(m,p,q):              # verbatim transcription of Watermark.gramUpper
    (j,(k,l)),(jj,(kk,ll)) = p,q
    if j==jj:
        if (k,l)==(kk,ll): return 2-m
        return 1 if (k==kk or l==ll) else 0
    if (j,jj)==(0,1): return 1 if (k-l)%m==(kk-ll)%m else 0
    if (j,jj)==(1,2): return 1 if (k+l)%m==(kk+ll)%m else 0
    if (j,jj)==(0,2): return 1 if (kk-ll)%m==(k+l+1)%m else 0
    return 0
def lean_gram(m,p,q): return lean_upper(m,p,q) if p[0]<=q[0] else lean_upper(m,q,p)
def eqs(m,p):
    j,(u,v)=p; e=np.exp(1j*np.pi/m); z=np.exp(2j*np.pi/m); A=e*z**u; B=e*z**v
    r=np.zeros((2,4),complex)
    if j==0: r[0,0]=1; r[0,1]=-A; r[1,2]=1; r[1,3]=-B
    if j==1: r[0,0]=1; r[0,2]=-A; r[1,1]=1; r[1,3]=-B
    if j==2: r[0,0]=1; r[0,3]=-A; r[1,1]=1; r[1,2]=-B
    return r
def geo(m,p,q):
    if p==q: return 2-m
    M=np.vstack([eqs(m,p),eqs(m,q)])
    return 1 if np.linalg.matrix_rank(M,tol=1e-8)<4 else 0
for m in [5,7,11]:
    L=[(j,(a,b)) for j in range(3) for a in range(m) for b in range(m)]
    # sanity: each line lies on the surface (check 3 random points)
    bad=0; pairs=0
    for i,p in enumerate(L):
        for q in L[i:]:
            pairs+=1
            if geo(m,p,q)!=lean_gram(m,p,q): bad+=1
    # control: the "wrong" shift k+l-1 in the (0,2) block must fail
    ctrl=sum(1 for p in L if p[0]==0 for q in L if q[0]==2 if geo(m,p,q)!=(1 if (q[1][0]-q[1][1])%m==(p[1][0]+p[1][1]-1)%m else 0))
    print(f"m={m}: {len(L)} lines, {pairs} pairs, mismatches {bad} -> {'MATCH' if bad==0 else 'FAIL'}; control (shift -1) mismatches {ctrl}")
    sys.stdout.flush()
