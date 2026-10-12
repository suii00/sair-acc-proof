import sys, itertools, json
sys.argv=[sys.argv[0]]
from greedy import search, red, inv, MS
def Y(a): return ((2,) if a>0 else (-2,))*abs(a)
fams={
 'A':lambda a,b,c: red(Y(a)+(1,)+Y(b)+(-1,)),
 'B':lambda a,b,c: red((1,)+Y(a)+(-1,)+Y(b)),
 'C':lambda a,b,c: red(Y(a)+(-1,)+Y(b)+(1,)+Y(c)),
}
res={}
R=range(-3,4)
for n in (2,3):
  for f,g in fams.items():
    for a,b,c in itertools.product(R,R,(R if f=='C' else [0])):
      w=g(a,b,c)
      key=(n,w)
      if key in res: continue
      r=search(MS(n,w),maxn=150000,maxlen=20)
      res[key]=None if r is None else len(r[1])
      print(n,f,a,b,c,w,res[key],flush=True)
