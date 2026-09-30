# Certificate for the exponent: Y = (+)_j (P_k + P_l + 3 P_{k-l} + 3 P_{k+l}) - 6m I (block-diagonal by family);
# claim  G Y G = 6 m^2 G  (as integer matrices).  Control: G Y G != 6 m G, and dropping the weight 3 fails.
import numpy as np, sys
from dl_profile import gram
def Ymat(m,w=(1,1,3,3),c=6):
    L=[(j,a,b) for j in range(3) for a in range(m) for b in range(m)]; n=len(L)
    Y=np.zeros((n,n),dtype=np.int64)
    for i,(j,a,b) in enumerate(L):
        for s,(jj,c2,d) in enumerate(L):
            if j!=jj: continue
            v=w[0]*(a==c2)+w[1]*(b==d)+w[2]*((a-b-c2+d)%m==0)+w[3]*((a+b-c2-d)%m==0)
            Y[i,s]=v
    return Y-c*m*np.eye(n,dtype=np.int64)
if __name__=="__main__":
 for m in map(int,sys.argv[1:]):
     G=gram(m); Y=Ymat(m); lhs=G@Y@G
     ok=np.array_equal(lhs,6*m*m*G)
     ctrl1=np.array_equal(lhs,6*m*G)
     Y2=Ymat(m,w=(1,1,1,1)); ctrl2=any(np.array_equal(G@Y2@G,k*G) for k in range(-50*m*m,50*m*m+1) if k!=0) if m<=7 else 'skip'
     # eigen/minimal polynomial check G(G+m)(G+2m)(G-3m)=0
     I=np.eye(G.shape[0],dtype=np.int64)
     mp=np.array_equal(G@(G+m*I)@(G+2*m*I)@(G-3*m*I),0*G)
     print(f"m={m}: GYG=6m^2G {ok} | control GYG=6mG {ctrl1} | weights(1,1,1,1) give scalar multiple {ctrl2} | minpoly G(G+m)(G+2m)(G-3m)=0 {mp}",flush=True)
