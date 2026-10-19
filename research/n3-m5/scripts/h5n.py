import itertools,sys
from bs import trivial, W
from cyc import red
def yp(k): return 'y'*k if k>=0 else 'Y'*(-k)
def inv(s): return ''.join(c.swapcase() for c in reversed(s))
n=int(sys.argv[1]); L=int(sys.argv[2]); A=int(sys.argv[3]); K=int(sys.argv[4]); ms=list(map(int,sys.argv[5:]))
gs=['']
for l in range(1,L+1):
    for t in itertools.product('xXyY',repeat=l):
        s=''.join(t)
        if all(s[i]!=s[i+1].swapcase() for i in range(l-1)): gs.append(s)
for m in ms:
  found=False
  for a in range(-A,A+1):
    src=red('x'+yp(a)+'x'+yp(-m)+'X'+yp(m))
    for k in range(-K,K+1):
      t=red('x'+inv(yp(-k)+'Xyxy'))
      for tt in (t,inv(t)):
        for g in gs:
          if trivial(W(g+src+inv(g)+inv(tt)),n): print('n',n,'m',m,'HIT a',a,'k',k,'conj',g,'inv' if tt!=t else '',flush=True); found=True; break
        if found: break
      if found: break
    if found: break
  if not found: print('n',n,'m',m,'no hit')
