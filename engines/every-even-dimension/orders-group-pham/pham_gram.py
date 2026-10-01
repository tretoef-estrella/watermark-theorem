#!/usr/bin/env python3
# regla297 -- end-to-end check of the model of section 1.3: the lattice H° = Z[G]e with Looijenga's form
#   (x e).(y e) = coefficient of 1 in x*ybar*theta,  theta = prod_{nu=0}^{N-1} (1-u_nu),
# and inside it  Hdg° = I_T e  and  T = I_B e.  Output: p-adic elementary divisors of the three Gram matrices.
# Expected: disc H° = p;  Hdg°: the rows of [AMV, Table 2];  T: the discriminant group of Hdg (Table 1).
# Usage: pham_gram.py n p [M]
import sys, itertools, numpy as np
n=int(sys.argv[1]); p=int(sys.argv[2]); r=n+1; N=n+2
M=int(sys.argv[3]) if len(sys.argv)>3 else 8
q=p**M
def matchable(a):
    cnt=[0]*p
    for x in a: cnt[x]+=1
    return all(cnt[x]==cnt[p-x] for x in range(1,p))
B=[];T=[]
for a in itertools.product(range(p), repeat=r-1):
    aa=(1,)+a; a0=(-sum(aa))%p; full=(a0,)+aa
    if 0 in full: continue
    (B if matchable(full) else T).append(aa)
R=list(itertools.product(range(p-1), repeat=r)); idx={g:i for i,g in enumerate(R)}
# coefficient function of theta on G = (Z/p)^r  (u_0 = (u_1...u_r)^{-1})
c={}
for S in itertools.product((0,1), repeat=r):
    s=(-1)**sum(S)
    g=tuple(S); c[g]=c.get(g,0)+s
    g2=tuple((x-1)%p for x in S); c[g2]=c.get(g2,0)-s
F=np.zeros((len(R),len(R)),dtype=object)
for i,g in enumerate(R):
    for j,h in enumerate(R):
        F[i,j]=c.get(tuple((x-y)%p for x,y in zip(g,h)),0)
def ev(Rp):
    rows=[]
    for a in Rp:
        e=[sum(x*y for x,y in zip(a,g))%p for g in R]
        for j in range(p-1):
            rows.append([(1 if x==j else 0)-(1 if x==p-1 else 0) for x in e])
    return rows
def col_kernel(top):
    nc=len(top[0]); A=[list(col) for col in zip(*top)]; K=[[1 if i==j else 0 for i in range(nc)] for j in range(nc)]
    piv=0
    for i in range(len(top)):
        while True:
            ix=[j for j in range(piv,nc) if A[j][i]!=0]
            if len(ix)<=1: break
            j0=min(ix,key=lambda j:abs(A[j][i]))
            for j in ix:
                if j==j0: continue
                qq=A[j][i]//A[j0][i]
                if qq:
                    A[j]=[x-qq*y for x,y in zip(A[j],A[j0])]; K[j]=[x-qq*y for x,y in zip(K[j],K[j0])]
        ix=[j for j in range(piv,nc) if A[j][i]!=0]
        if ix:
            j=ix[0]; A[piv],A[j]=A[j],A[piv]; K[piv],K[j]=K[j],K[piv]; piv+=1
    return K[piv:]
def smith_vals(Gm):
    # p-adic elementary divisors of a (possibly degenerate) integer matrix; stops when the rest is 0 mod p^M
    W=np.array([[int(x)%q for x in row] for row in Gm],dtype=object); vals=[]
    rows=list(range(W.shape[0])); cols=list(range(W.shape[1]))
    while rows:
        best=None
        for v in range(M):
            pv1=p**(v+1)
            for i in rows:
                for j in cols:
                    if W[i,j]%pv1!=0: best=(v,i,j); break
                if best: break
            if best: break
        if not best: break
        v,i,j=best; pv=p**v; u=W[i,j]//pv; uinv=pow(int(u),-1,p**(M-v))
        for i2 in rows:
            if i2==i: continue
            m_=(W[i2,j]//pv)*uinv%(p**(M-v))
            if m_:
                for j2 in cols: W[i2,j2]=(W[i2,j2]-m_*W[i,j2])%q
        rows.remove(i); cols.remove(j); vals.append(v)
    h={}
    for v in vals: h[v]=h.get(v,0)+1
    return len(vals),sum(vals),dict(sorted(h.items()))
def gram(K):
    Km=np.array(K,dtype=object)           # rows = lattice vectors (coordinates on R)
    return Km.dot(F).dot(Km.T)
print('(n,p)=(%d,%d)  |A|=%d  |B|=%d  |T|=%d'%(n,p,(len(B)+len(T))*(p-1),len(B)*(p-1),len(T)*(p-1)))
print('H°   : rank, v_p(disc), exponents =',smith_vals(F))
if T:
    print('Hdg° : rank, v_p(disc), exponents =',smith_vals(gram(col_kernel(ev(T)))))
print('T(X) : rank, v_p(disc), exponents =',smith_vals(gram(col_kernel(ev(B)))))
print('FIN-OK')
