# Galois orbits of non-Hodge characters, n = 4: classify by natural invariants and look for classes of size 4 (p=5) and 120 (p=7).
import itertools, sys
from collections import Counter
def esym(a,r,p):
    e=[1]+[0]*r
    for x in a:
        for j in range(r,0,-1): e[j]=(e[j]+x*e[j-1])%p
    return e[r]
def run(n,p):
    N=n+2; cls=Counter(); t=0
    for a in itertools.product(range(1,p),repeat=N-1):
        last=(-sum(a))%p
        if last==0: continue
        a=a+(last,); c=Counter(a)
        if all(c[v]==c[p-v] for v in c): continue
        t+=1
        shape=tuple(sorted(c.values(),reverse=True))
        npairs=sum(min(c[v],c[p-v]) for v in c if v<p-v)
        ws=tuple(sorted(sum((s*x)%p for x in a)//p for s in range(1,p)))
        wmin=ws[0]
        tri=any((a[i]+a[j]+a[l])%p==0 for i,j,l in itertools.combinations(range(N),3))
        cls[('shape',shape)]+=1; cls[('pairs',npairs)]+=1; cls[('wmin',wmin)]+=1; cls[('tri',tri)]+=1
        cls[('e3=0',esym(a,3,p)==0)]+=1; cls[('e5=0',esym(a,5,p)==0)]+=1; cls[('nvals',len(c))]+=1
        cls[('pairs,wmin',npairs,wmin)]+=1; cls[('weights',ws)]+=1
    print((n,p),'T orbits',t//(p-1))
    for key,v in sorted(cls.items(),key=str): print('   ',key,v/(p-1))
for p in (3,5,7): run(4,p)
print('FIN-OK')
