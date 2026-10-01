# Orbits of non-Hodge characters of the Fermat variety (n,p), and the values of e_3, e_5 mod p on them.
import itertools, sys
from collections import Counter
def esym(a,r,p):
    e=[1]+[0]*r
    for x in a:
        for j in range(r,0,-1): e[j]=(e[j]+x*e[j-1])%p
    return e[r]
def pairable(a,p):
    c=Counter(a)
    return all(c[v]==c[p-v] for v in c)
def run(n,p):
    N=n+2
    seen=set(); stats=Counter(); t=0
    for a in itertools.product(range(1,p),repeat=N-1):
        last=(-sum(a))%p
        if last==0: continue
        a=a+(last,)
        if pairable(a,p): continue
        # canonical rep of the orbit under scalars and permutations is not needed: count characters
        e3=esym(a,3,p); e5=esym(a,5,p) if N>=5 else None
        w=sum(a)//p
        stats[(e3==0, e5==0 if e5 is not None else None)]+=1
        t+=1
    print((n,p),'T characters',t,'orbits',t//(p-1))
    for k,v in sorted(stats.items(),key=str): print('   e3==0,e5==0 :',k,'chars',v,'orbits',v/(p-1))
for (n,p) in [(2,5),(2,7),(4,3),(6,3),(8,3),(4,5),(4,7)]:
    run(n,p)
print('FIN-OK')
