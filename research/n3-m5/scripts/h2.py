# H2: automorphism phi: x -> y^j x y^k, y -> y fixes r0 = X y^n x Y^(n+1) up to conjugation.
# It sends MS(n, wA m) to (r0', x y^s x y^-m X y^m) with s = j+k (after conjugating by y^-j).
import sys,time
from cyc import search, red
n=int(sys.argv[1]); m=int(sys.argv[2]); maxn=int(sys.argv[3]); maxlen=int(sys.argv[4])
def yp(k): return 'y'*k if k>=0 else 'Y'*(-k)
r0='X'+'y'*n+'x'+'Y'*(n+1)
for s in map(int,sys.argv[5:]):
    r1=red('x'+yp(s)+'x'+yp(-m)+'X'+yp(m))
    t=time.time(); path,N=search(r0,r1,maxn,maxlen)
    print('s',s,'r1',r1,'moves',None if path is None else len(path),'states',N,'t',round(time.time()-t),flush=True)
    if path:
        for info,q in path: print('  ',info,'->',q)
