# Re-check (30 Sep, for the certificate) of the W4 formulas with the correct (0,2) shifts:
# G*pb(0,+1,u) = -m pb(0,+1,u) + m pb(2,-1,u(x-1));  G*pb(2,-1,u) = -m pb(2,-1,u) + m pb(0,+1,u(x+1)).
# Expected: all True for m = 5, 7, 11 and every u in a basis of Z0; the swapped shifts (control) False.
import numpy as np
exec(open('w1_gram.py').read().split("for m in [5,7,11]")[0])
for m in [5,7,11]:
    I=idx(m); pos={p:i for i,p in enumerate(I)}; n=len(I)
    G=np.array([[G_entry(m,p,q) for q in I] for p in I],dtype=object)
    pen=lambda t,k,l: l%m if t=='inf' else (k+t*l)%m
    def pb(j,t,u):
        v=np.zeros(n,dtype=object)
        for k in range(m):
            for l in range(m): v[pos[(j,k,l)]]=u[pen(t,k,l)]
        return v
    ok=True; ctrl=True
    for x0 in range(1,m):
        u=[0]*m; u[0]=-1; u[x0]=1
        sh=lambda s:[u[(x-s)%m] for x in range(m)]
        ok&=all(not any(G.dot(pb(j,t,u))) for j in range(3) for t in ['inf',0])
        ok&=all(all(G.dot(pb(j,t,u))==-m*pb(j,t,u)) for j in range(3) for t in range(2,m-1))
        ok&=all(G.dot(pb(0,m-1,u))==-m*pb(0,m-1,u)+m*pb(1,m-1,u))
        ok&=all(G.dot(pb(1,m-1,u))==-m*pb(1,m-1,u)+m*pb(0,m-1,u))
        ok&=all(G.dot(pb(1,1,u))==-m*pb(1,1,u)+m*pb(2,1,u))
        ok&=all(G.dot(pb(2,1,u))==-m*pb(2,1,u)+m*pb(1,1,u))
        ok&=all(G.dot(pb(0,1,u))==-m*pb(0,1,u)+m*pb(2,m-1,sh(1)))
        ok&=all(G.dot(pb(2,m-1,u))==-m*pb(2,m-1,u)+m*pb(0,1,sh(m-1)))
        ctrl&=all(G.dot(pb(0,1,u))==-m*pb(0,1,u)+m*pb(2,m-1,sh(m-1)))
    print(f"m={m}: all W4 formulas on a basis of Z0: {ok}; control (swapped shift) holds: {ctrl}")
print("FIN-OK")
