# H3 landscape: which (r0, x y^a x y^b X y^c) (n=3) are solved quickly by cyclic search? (experiment)
import sys,time
from cyc import search, red
from bs import trivial, W
n=3; r0='X'+'y'*n+'x'+'Y'*(n+1)
def yp(k): return 'y'*k if k>=0 else 'Y'*(-k)
B=int(sys.argv[1]); A=int(sys.argv[2]); maxn=int(sys.argv[3])
for b in range(-B,B+1):
  for c in range(-B,B+1):
    for a in range(-A,A+1):
      r1=red('x'+yp(a)+'x'+yp(b)+'X'+yp(c))
      path,N=search(r0,r1,maxn,24)
      print(a,b,c,r1,'SOLVED' if path else '-',len(path) if path else N,flush=True)
