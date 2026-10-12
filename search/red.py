import sys
sys.argv=[sys.argv[0]]
from greedy import *
def Y(a): return ((2,) if a>0 else (-2,))*abs(a)
S={1:'x',-1:'X',2:'y',-2:'Y'}
s=lambda w:''.join(S[a] for a in w)
for n in range(2,6):
  for m in list(range(-7,0))+list(range(1,8)):
    best=None
    for q in range(-8,9):
      j=m-q*n
      w=red(Y(-j)+(1,)+Y(j-q)+(-1,))
      if best is None or len(w)<len(best[0]): best=(w,q,j)
    w,q,j=best
    r=search(MS(n,w),maxn=400000,maxlen=28)
    print(n,m,'q=%d j=%d'%(q,j),s(w),'.' if r is None else len(r[1]),flush=True)
