import sys,time
from cyc import *
# usage: n maxn maxlen word...   (word = second-relator parameter w; MS(n,w))
n=int(sys.argv[1]); maxn=int(sys.argv[2]); maxlen=int(sys.argv[3])
for w in sys.argv[4:]:
    t=time.time(); a,b=MS(n,w); path,N=search(a,b,maxn,maxlen)
    print(n,w,a,b,'moves',None if path is None else len(path),'states',N,'t',round(time.time()-t),flush=True)
    if path:
        for info,q in path: print('  ',info,'->',q)
