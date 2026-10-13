import sys
q=int(sys.argv[1]); stop=sys.argv[2]; sys.argv=[sys.argv[0]]
from greedy import *
def Y(a): return ((2,) if a>0 else (-2,))*abs(a)
S={1:'x',-1:'X',2:'y',-2:'Y'}
s=lambda w:''.join(S[a] for a in w) or '1'
w=red((-2,1)+Y(1-q)+(-1,))
p0=MS(2,w)
r=search(p0,maxn=600000,maxlen=30)
A=(); eps=1
for mv,a,b in r[1]:
  if mv[1]==1:
    if mv[0]=='conj': A=red((mv[2],)+A)
    if mv[0]=='inv': eps=-eps
  if s(b[1])==stop: break
print('s_q =',s(red(p0[1])),' A =',s(A),' eps =',eps,' final slot1 =',s(b[1]), 'slot0=',s(b[0]))
