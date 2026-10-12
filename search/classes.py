import sys
n=int(sys.argv[1]); budget=int(sys.argv[2]); sys.argv=[sys.argv[0]]
from greedy import *
def Y(a): return ((2,) if a>0 else (-2,))*abs(a)
S={1:'x',-1:'X',2:'y',-2:'Y'}
s=lambda w:''.join(S[a] for a in w)
N=n*(n+1)
for r in range(N):
  if r%n==0 or r==n+1 or r==N-(n+1) or (r==1) : print(n,r,'known'); continue
  done=False
  cands=[]
  for t in range(-2,3):
    m=r+t*N
    for q in range(-6,7):
      j=m-q*n
      w=red(Y(-j)+(1,)+Y(j-q)+(-1,))
      cands.append((len(w),m,q,j,w))
  cands.sort()
  seen=set()
  for L,m,q,j,w in cands[:8]:
    if w in seen: continue
    seen.add(w)
    res=search(MS(n,w),maxn=budget,maxlen=30)
    if res:
      print(n,r,'SOLVED m=%d q=%d j=%d w=%s moves=%d'%(m,q,j,s(w),len(res[1])),flush=True); done=True; break
  if not done: print(n,r,'UNSOLVED tried',[s(w) for w in seen],flush=True)
