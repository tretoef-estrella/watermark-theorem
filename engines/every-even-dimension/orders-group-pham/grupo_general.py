#!/usr/bin/env python3
# regla297 -- the discriminant GROUP: structure of Z[G]/(I_B + I_T) as an abelian group,
# computed exactly over Z:  Z[G]/(I_B+I_T) = E_T(Z[G]) / E_T(ker E_B).
# Usage: grupo_general.py n m      (any degree m >= 3; small cells only)
# Hodge characters: a in A with <t a> := sum_nu {t a_nu / m} = k+1 for every unit t mod m.
import sys, itertools
from sympy import Matrix, ZZ, Poly, cyclotomic_poly, symbols, totient
from math import gcd
from sympy.matrices.normalforms import smith_normal_form
n=int(sys.argv[1]); p=int(sys.argv[2]); r=n+1
m=p; k=n//2; X_=symbols('x'); Phi=Poly(cyclotomic_poly(m,X_),X_,domain='ZZ'); phi=int(totient(m))
red=[]                                      # x^e mod Phi_m as integer vectors of length phi
for e in range(m):
    c=Poly(X_**e,X_,domain='ZZ').rem(Phi).all_coeffs()[::-1]; c=[int(x) for x in c]+[0]*(phi-len(c)); red.append(c)
units=[t for t in range(1,m) if gcd(t,m)==1]
def hodge(full):
    return all(sum((t*x)%m for x in full)==(k+1)*m for t in units)
seen=set(); B=[]; T=[]
for a in itertools.product(range(m), repeat=r):
    a0=(-sum(a))%m; full=(a0,)+a
    if 0 in full or a in seen: continue
    for t in units: seen.add(tuple((t*x)%m for x in a))      # one representative per Galois orbit
    (B if hodge(full) else T).append(a)
G=list(itertools.product(range(m), repeat=r))
def ev(R):
    rows=[]
    for a in R:
        e=[sum(x*y for x,y in zip(a,g))%m for g in G]
        for j in range(phi):
            rows.append([red[x][j] for x in e])
    # Galois orbits of non-primitive characters have fewer than phi conjugates: drop dependent rows later (rank handled by HNF)
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
print('(n,m)=(%d,%d)  orbits B=%d T=%d  invariants of Z[G]/(I_B+I_T):'%(n,m,len(B),len(T)),dict(sorted(hist.items())))
print('FIN-OK')
