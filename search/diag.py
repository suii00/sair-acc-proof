import sys
sys.argv=[sys.argv[0]]
from greedy import *
for n in range(2,6):
  row=[]
  for m in list(range(-6,0))+list(range(1,7)):
    Ym=((-2,) if m>0 else (2,))*abs(m)
    w=red(Ym+(1,)+tuple(-a for a in Ym)+(-1,))
    r=search(MS(n,w),maxn=300000,maxlen=28)
    row.append('.' if r is None else str(len(r[1])))
  print(n,' '.join('%3s'%c for c in row),flush=True)
