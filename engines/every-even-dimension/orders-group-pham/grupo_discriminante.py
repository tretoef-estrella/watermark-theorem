#!/usr/bin/env python3
# regla297 -- the discriminant GROUP: structure of Z[G]/(I_B + I_T) as an abelian group,
# computed exactly over Z:  Z[G]/(I_B+I_T) = E_T(Z[G]) / E_T(ker E_B).
# Usage: grupo_discriminante.py n p      (small cells only)
import sys, itertools
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
n=int(sys.argv[1]); p=int(sys.argv[2]); r=n+1
def matchable(a):
    cnt=[0]*p
    for x in a: cnt[x]+=1
    return all(cnt[x]==cnt[p-x] for x in range(1,p))
B=[];T=[]
for a in itertools.product(range(p), repeat=r-1):
    aa=(1,)+a; a0=(-sum(aa))%p; full=(a0,)+aa
    if 0 in full: continue
    (B if matchable(full) else T).append(aa)
G=list(itertools.product(range(p-1), repeat=r))
def ev(R):
    rows=[]
    for a in R:
        e=[sum(x*y for x,y in zip(a,g))%p for g in G]
        for j in range(p-1):
            rows.append([(1 if x==j else 0)-(1 if x==p-1 else 0) for x in e])
    return rows
def col_hnf(top, bottom):
    # unimodular column operations bringing `top` to column echelon form; returns (top, bottom) transformed
    A=[list(c) for c in zip(*top)]; Bm=[list(c) for c in zip(*bottom)]   # lists of columns
    nc=len(A); nr=len(top); piv=0
    for i in range(nr):
        while True:
            idx=[j for j in range(piv,nc) if A[j][i]!=0]
            if len(idx)<=1: break
            j0=min(idx,key=lambda j:abs(A[j][i]))
            for j in idx:
                if j==j0: continue
                qq=A[j][i]//A[j0][i]
                if qq:
                    A[j]=[x-qq*y for x,y in zip(A[j],A[j0])]; Bm[j]=[x-qq*y for x,y in zip(Bm[j],Bm[j0])]
        idx=[j for j in range(piv,nc) if A[j][i]!=0]
        if idx:
            j=idx[0]; A[piv],A[j]=A[j],A[piv]; Bm[piv],Bm[j]=Bm[j],Bm[piv]; piv+=1
    return A,Bm,piv
EB=ev(B); ET=ev(T); c=len(G)
Id=[[1 if i==j else 0 for j in range(c)] for i in range(c)]
A,K,rk=col_hnf(EB,Id)
ker=K[rk:]                                   # saturated Z-basis of ker E_B = I_B (as vectors of length c)
assert all(all(x==0 for x in A[j]) for j in range(rk,c))
# L_T basis: column HNF of E_T ; and coordinates of E_T(ker) in it
AT,_,rT=col_hnf(ET,Id)
basisT=AT[:rT]                               # columns, echelon
img=[[sum(ET[i][j]*v[j] for j in range(c)) for i in range(len(ET))] for v in ker]
# solve img = basisT * X  (echelon => forward substitution over Z)
pivrow=[]
for col in basisT:
    pivrow.append(next(i for i,x in enumerate(col) if x!=0))
X=[]
for v in img:
    v=list(v); coef=[]
    for col,pr in zip(basisT,pivrow):
        qq,rem=divmod(v[pr],col[pr]); assert rem==0
        coef.append(qq); v=[x-qq*y for x,y in zip(v,col)]
    assert all(x==0 for x in v); X.append(coef)
S=smith_normal_form(Matrix(X).T, domain=ZZ)
d=[abs(S[i,i]) for i in range(min(S.shape))]
hist={}
for x in d: hist[x]=hist.get(x,0)+1
print('(n,p)=(%d,%d)  |B|=%d |T|=%d  invariants of Z[G]/(I_B+I_T):'%(n,p,len(B)*(p-1),len(T)*(p-1)),dict(sorted(hist.items())))
print('FIN-OK')
