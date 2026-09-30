import sys; sys.path.insert(0,'.'); import numpy as np
exec(open('w1_gram.py').read().split("for m in [5,7,11]")[0])
m=5; I=idx(m); pos={p:i for i,p in enumerate(I)}; n=len(I)
G=np.array([[G_entry(m,p,q) for q in I] for p in I],dtype=object)
def pen(t,k,l): return l%m if t=='inf' else (k+t*l)%m
def pb(j,t,u):
    v=np.zeros(n,dtype=object)
    for k in range(m):
        for l in range(m): v[pos[(j,k,l)]]=u[pen(t,k,l)]
    return v
u=[1,-1,0,0,0]; us=lambda s:[u[(x-s)%m] for x in range(m)]
tests={'axis':all(not any(G.dot(pb(j,t,u))) for j in range(3) for t in ['inf',0]),
 'live':all(all(G.dot(pb(j,t,u))==-m*pb(j,t,u)) for j in range(3) for t in range(2,m-1)),
 '0,-1':all(G.dot(pb(0,m-1,u))==-m*pb(0,m-1,u)+m*pb(1,m-1,u)),
 '1,-1':all(G.dot(pb(1,m-1,u))==-m*pb(1,m-1,u)+m*pb(0,m-1,u)),
 '1,+1':all(G.dot(pb(1,1,u))==-m*pb(1,1,u)+m*pb(2,1,u)),
 '2,+1':all(G.dot(pb(2,1,u))==-m*pb(2,1,u)+m*pb(1,1,u))}
for s in range(m):
    tests[f'0,+1 s={s}']=all(G.dot(pb(0,1,u))==-m*pb(0,1,u)+m*pb(2,m-1,us(s)))
    tests[f'2,-1 s={s}']=all(G.dot(pb(2,m-1,u))==-m*pb(2,m-1,u)+m*pb(0,1,us(s)))
print(tests)
