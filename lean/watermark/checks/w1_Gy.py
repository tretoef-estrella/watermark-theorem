import importlib.util,sys
spec=importlib.util.spec_from_file_location("w","w1_gram.py")
src=open("w1_gram.py").read().split("for m in [5,7,11]")[0]; exec(src)
for m in [5,7,11]:
    I=idx(m); n=len(I); ok=True; exc=set()
    for t in range(1,m):
        for c in range(m):
            y=[1 if (p[0]==0 and (p[1]+t*p[2])%m==c) else 0 for p in I]
            Gy=[sum(G_entry(m,p,q)*y[b] for b,q in enumerate(I)) for p in I]
            r=[Gy[a]+m*y[a] for a in range(n)]   # should be 2 on fam0, and fam1/fam2 parts
            f0=[r[a] for a in range(n) if I[a][0]==0]; f1=[r[a] for a in range(n) if I[a][0]==1]; f2=[r[a] for a in range(n) if I[a][0]==2]
            ok &= all(v==2 for v in f0)
            for name,f,tt in (("1",f1,m-1),("2",f2,1)):
                if all(v==1 for v in f): continue
                vals=sorted(set(f))
                if t==tt and vals==[0,m] and f.count(m)==m: exc.add((name,t)); continue
                ok=False; print("FAIL",m,t,c,name,vals)
    print(f"m={m} Gy formulas ok={ok} exceptional (family,slope)={sorted(exc)}")
