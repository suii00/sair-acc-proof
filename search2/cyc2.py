# Variant: supermoves r_i <- r_i * (rotation of r_j^{±1})^k for k = 1..K, and weighted priority.
import sys,time,heapq
from cyc import red,cred,inv,canon,rots,key,done,MS
K=int(sys.argv[4]); WT=float(sys.argv[5])
def nbrs(p):
    a,b=p
    for (u,v) in ((a,b),(b,a)):
        RU=[u[k:]+u[:k] for k in range(len(u))] or ['']
        out=set()
        for rv in rots(v):
            for k in range(1,K+1):
                pw=rv*k
                for ru in RU: out.add(canon(cred(ru+pw)))
        for c in out: yield key(c,v),(u,v,c)
def score(q): return max(len(q[0]),len(q[1]))*WT+len(q[0])+len(q[1])
def search(a,b,maxn,maxlen):
    p0=key(canon(cred(a)),canon(cred(b))); seen={p0:None}; pq=[(score(p0),0,p0)]; c=0
    while pq:
        _,_,p=heapq.heappop(pq)
        if done(p):
            path=[];q=p
            while seen[q]: path.append((seen[q][1],q)); q=seen[q][0]
            return path[::-1],len(seen)
        for q,info in nbrs(p):
            if q in seen or max(len(q[0]),len(q[1]))>maxlen: continue
            seen[q]=(p,info); c+=1; heapq.heappush(pq,(score(q),c,q))
        if len(seen)>maxn: return None,len(seen)
    return None,len(seen)
n=int(sys.argv[1]); maxn=int(sys.argv[2]); maxlen=int(sys.argv[3])
for w in sys.argv[6:]:
    t=time.time(); a,b=MS(n,w); path,N=search(a,b,maxn,maxlen)
    print(n,w,'K',K,'WT',WT,'moves',None if path is None else len(path),'states',N,'t',round(time.time()-t),flush=True)
    if path:
        for info,q in path: print('  ',info,'->',q)
