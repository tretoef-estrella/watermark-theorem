#!/usr/bin/env python3
# regla297 -- delta invariants of the orders A_Y = image of Z_p[G] in prod_{orbits in Y} Z_p[zeta]
# for Y = A (all primitive characters), B (Hodge characters), T (the others).
# Usage: delta_ordenes.py n p [M]
# Checks, with E = v_p disc Hdg known:  l := dA - dB - dT == E ;  2dA == 1 + c*alpha ;
#   2dB == 1 + c*B - E ;  2dT == c*t - E ,   c = 2k(p-2)-1.
import sys, os, itertools, numpy as np
n=int(sys.argv[1]); p=int(sys.argv[2]); k=n//2; r=n+1; N=n+2
M=int(sys.argv[3]) if len(sys.argv)>3 else {3:19,5:13,7:11,11:9,13:8}[p]
q=p**M
DT=np.int32 if p**(2*M) < 2**31 else np.int64
def matchable(a):
    # a: tuple of N nonzero residues; can it be split in pairs {x,-x}?
    cnt=[0]*p
    for x in a: cnt[x]+=1
    return all(cnt[x]==cnt[p-x] for x in range(1,p))
reps={'A':[], 'B':[], 'T':[]}
for a in itertools.product(range(p), repeat=r-1):
    aa=(1,)+a                     # orbit representative: a_1 = 1
    a0=(-sum(aa))%p
    full=(a0,)+aa
    if 0 in full: continue
    reps['A'].append(aa)
    (reps['B'] if matchable(full) else reps['T']).append(aa)
# RED=1: only the group elements with all coordinates in 0..p-2. They span each A_Y over Z_p, because
# N_i = 1+t_i+...+t_i^{p-1} lies in I_A and N_i = y_i^{p-1} mod p (Nakayama). SETS=B restricts the run.
RED=os.environ.get('RED','0')=='1'; SETS=os.environ.get('SETS','ABT')
G=np.array(list(itertools.product(range(p-1 if RED else p), repeat=r)),dtype=np.int64)
def evalmat(R):
    R=np.array(R,dtype=np.int64)
    e=((R@G.T)%p).astype(np.int8)            # (#reps) x |G| exponents
    W=np.zeros((len(R)*(p-1),G.shape[0]),dtype=DT)
    last=(e==p-1)
    for j in range(p-1):
        W[j::p-1,:]=(e==j).astype(DT)-last.astype(DT)
    del e,last
    W%=q
    return W
def smith_vals(W):
    nr=W.shape[0]; active=np.ones(nr,dtype=bool); vals=[]
    for v in range(M):
        pv=p**v; pv1=pv*p
        for i in range(nr):
            if not active[i]: continue
            row=W[i]
            nz=np.nonzero(row%pv1)[0]
            if nz.size==0: continue
            j=nz[0]; u=int(row[j])//pv; qq=p**(M-v)
            uinv=pow(u,-1,qq)
            active[i]=False; vals.append(v)
            idx=np.nonzero(active)[0]
            if idx.size==0: break
            mult=((W[idx,j]//pv)%qq)*uinv%qq
            nzm=np.nonzero(mult)[0]
            if nzm.size:
                rows=idx[nzm]; mm=mult[nzm].astype(DT); rowc=row.copy()
                for s0 in range(0,rows.size,256):      # chunks: bounded temporaries
                    rr=rows[s0:s0+256]
                    W[rr]=(W[rr]-mm[s0:s0+256,None]*rowc[None,:])%q
        if not active.any(): break
    if active.any(): raise SystemExit('rank deficient or M too small: %d rows left'%active.sum())
    return vals
out={}
for name in 'ABT':
    if not reps[name] or name not in SETS: out[name]=(len(reps[name]),0,{}); continue
    vals=smith_vals(evalmat(reps[name]))
    hist={}
    for v in vals: hist[v]=hist.get(v,0)+1
    out[name]=(len(reps[name]),sum(vals),hist)
    print(name,'orbits',len(reps[name]),'delta',sum(vals),'elem.div. exponents',dict(sorted(hist.items())),flush=True)
al,dA,_=out['A']; B,dB,_=out['B']; t,dT,_=out['T']; c=2*k*(p-2)-1
l=dA-dB-dT
print('(n,p)=(%d,%d) alpha=%d B=%d t=%d c=%d'%(n,p,al,B,t,c))
print('l = dA-dB-dT =',l)
print('2dA-(1+c*alpha) =',2*dA-(1+c*al),' [0 expected: disc H_prim = p]')
print('E from B-side: 1+c*B-2dB =',1+c*B-2*dB)
print('E from T-side: c*t-2dT   =',c*t-2*dT)
print('FIN-OK')
