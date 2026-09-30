import numpy as np, sys
from dl_profile import gram
from collections import Counter
for m in map(int,sys.argv[1:]):
    G=gram(m).astype(float); w=np.linalg.eigvalsh(G)
    c=Counter(np.round(w,6)); print(m, sorted(c.items()))
