# Cyclic-canonical AC search (rank 2). States: unordered pair of cyclic words up to inversion.
# Move: r_i <- cyclic reduction of (rotation of r_i) * (rotation of r_j^{±1}). Each such move is a composition of
# official AC steps (conjugations, inversion, mulRight), so a found path certifies AC-triviality (emission done separately).
import heapq, sys, time
INV={'x':'X','X':'x','y':'Y','Y':'y'}
def red(w):
    o=[]
    for a in w:
        if o and o[-1]==INV[a]: o.pop()
        else: o.append(a)
    return ''.join(o)
def cred(w):
    w=red(w)
    while len(w)>1 and w[0]==INV[w[-1]]: w=w[1:-1]
    return w
def inv(w): return ''.join(INV[a] for a in reversed(w))
def canon(w):
    if not w: return w
    v=inv(w); n=len(w)
    return min(min(w[k:]+w[:k] for k in range(n)), min(v[k:]+v[:k] for k in range(n)))
def rots(w):
    s=set()
    for u in (w,inv(w)):
        for k in range(len(u)): s.add(u[k:]+u[:k])
    return s
def key(a,b): return (a,b) if a<=b else (b,a)
def nbrs(p):
    a,b=p
    for (u,v) in ((a,b),(b,a)):
        RU=[u[k:]+u[:k] for k in range(len(u))] or ['']
        RV=rots(v)
        out=set()
        for ru in RU:
            for rv in RV:
                out.add(canon(cred(ru+rv)))
        for c in out: yield key(c,v),(u,v,c)
def done(p): return sorted(len(w) for w in p)==[1,1] and {p[0].lower(),p[1].lower()}=={'x','y'}
def search(a,b,maxn,maxlen,w_len=1.0,log=None):
    p0=key(canon(cred(a)),canon(cred(b)))
    seen={p0:None}; pq=[(len(p0[0])+len(p0[1]),0,p0)]; c=0; t=time.time()
    while pq:
        L,_,p=heapq.heappop(pq)
        if done(p):
            path=[];q=p
            while seen[q]: path.append((seen[q][1],q)); q=seen[q][0]
            return path[::-1],len(seen)
        for q,info in nbrs(p):
            if q in seen or max(len(q[0]),len(q[1]))>maxlen: continue
            seen[q]=(p,info); c+=1
            heapq.heappush(pq,(len(q[0])+len(q[1]),c,q))
        if len(seen)>maxn: return None,len(seen)
    return None,len(seen)
def MS(n,w): return 'X'+'y'*n+'x'+'Y'*(n+1), red('x'+inv(w))
def wA(m): return red(('Y'*m if m>=0 else 'y'*(-m))+'x'+('y'*m if m>=0 else 'Y'*(-m))+'X')
if __name__=='__main__':
    n=int(sys.argv[1]); maxn=int(sys.argv[2]); maxlen=int(sys.argv[3])
    for m in map(int,sys.argv[4:]):
        t=time.time(); a,b=MS(n,wA(m))
        path,N=search(a,b,maxn,maxlen)
        print(n,m,a,b,'moves',None if path is None else len(path),'states',N,'t',round(time.time()-t),flush=True)
        if path:
            for info,q in path: print('  ',q)
