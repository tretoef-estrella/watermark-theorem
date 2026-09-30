# Probe for odd composite m: does the Double Ladder machinery survive?
# (1) minimal polynomial G(G+m)(G+2m)(G-3m)=0 ; (2) G Y G = 6 m^2 G ; (3) disc profile per prime p | m
import numpy as np, sys
from dl_profile import gram, profile
from dl_cert import Ymat
from sympy import factorint
for m in map(int,sys.argv[1:]):
    G=gram(m); n=G.shape[0]; I=np.eye(n,dtype=np.int64)
    mp=np.array_equal(G@(G+m*I)@(G+2*m*I)@(G-3*m*I),0*G)
    Y=Ymat(m); cert=np.array_equal(G@Y@G,6*m*m*G)
    out=[]
    tot={}
    for p,e in factorint(m).items():
        E=2*e+2
        pr=profile(G,p,E); out.append((p,dict(sorted(pr.items(),key=lambda t:str(t[0])))))
        tot[p]=sum(v*c for v,c in pr.items() if isinstance(v,int))
    exp_w=3*(m-3)**2
    print(f"m={m}: minpoly {mp} | GYG=6m^2G {cert} | profiles {out} | log_p disc {tot} vs watermark law m^{exp_w} -> {[e*exp_w for p,e in factorint(m).items()]}",flush=True)
