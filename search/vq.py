import sys
Q=[int(a) for a in sys.argv[1:]]; sys.argv=[sys.argv[0]]
from greedy import *
def Y(a): return ((2,) if a>0 else (-2,))*abs(a)
S={1:'x',-1:'X',2:'y',-2:'Y'}
s=lambda w:''.join(S[a] for a in w) or '1'
for q in Q:
  w=red((-2,1)+Y(1-q)+(-1,))
  r=search(MS(2,w),maxn=600000,maxlen=30)
  print('### q=%d w=%s'%(q,s(w)), None if r is None else len(r[1]))
  if r and '-v' in Q.__repr__(): pass
  if r:
    for mv,a,b in r[1]: print('  ',mv,s(b[0]),'|',s(b[1]))
