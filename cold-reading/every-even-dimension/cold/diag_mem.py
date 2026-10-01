import numpy as np, resource
def mem(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20
p=11; PM=p**9
rng=np.random.default_rng(1)
A=rng.integers(0,PM,size=(1000,910),dtype=np.int64)
print('start',mem())
row=A[0].copy()
f=A[1:,0]%PM
x=(f[:,None]*row[None,:])
print('after product',mem(), x.dtype, x.nbytes/2**20)
y=x%PM
print('after mod',mem())
z=A[1:]-y
print('after sub',mem())
w=np.nonzero(f)[0]
B=A[1+w]
print('after fancy',mem())
for i in range(50):
    A[1+w]=(A[1+w]-(f[w,None]*row[None,:])%PM)%PM
print('after 50 iterations',mem())
