# H5: is r1(wA 5) (or its phi-images x y^a x Y^5 X y^5) G-conjugate in BS(3,4) to x*w_k^-1 (w_k = y^-k X y x y), the
# family AC-equivalent to AK(3)? A hit would link MS(3,wA 5) to AK(3) (hardness evidence / equivalence). Experiment.
import itertools,sys
from bs import trivial, W
from cyc import red
def yp(k): return 'y'*k if k>=0 else 'Y'*(-k)
def inv(s): return ''.join(c.swapcase() for c in reversed(s))
L=int(sys.argv[1]); A=int(sys.argv[2]); K=int(sys.argv[3])
gs=['']
for l in range(1,L+1):
    for t in itertools.product('xXyY',repeat=l):
        s=''.join(t)
        if all(s[i]!=s[i+1].swapcase() for i in range(l-1)): gs.append(s)
for a in range(-A,A+1):
  src=red('x'+yp(a)+'xYYYYYXyyyyy')
  for k in range(-K,K+1):
    wk=yp(-k)+'Xyxy'; t=red('x'+inv(wk))
    for tt in (t,inv(t)):
      for g in gs:
        if trivial(W(g+src+inv(g)+inv(tt)),3): print('HIT',a,k,g,flush=True); break
print('done')
