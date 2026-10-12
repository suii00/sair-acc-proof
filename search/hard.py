import sys
sys.argv=[sys.argv[0]]
from greedy import *
S={1:'x',-1:'X',2:'y',-2:'Y'}
s=lambda w:''.join(S[a] for a in w)
P={'x':1,'X':-1,'y':2,'Y':-2}
for ws in ['YxYX','yxyX','yyxYX','YYxyX','YxyyyX','yxYYYX']:
  w=tuple(P[c] for c in ws)
  for ml in (34,40):
    r=search(MS(3,w),maxn=4000000,maxlen=ml)
    print(ws,ml,None if r is None else len(r[1]),flush=True)
    if r: break
