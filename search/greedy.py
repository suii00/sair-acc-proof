import heapq, sys
# letters: 1=x,-1=X,2=y,-2=Y
def red(w):
    out=[]
    for a in w:
        if out and out[-1]==-a: out.pop()
        else: out.append(a)
    return tuple(out)
def inv(w): return tuple(-a for a in reversed(w))
def moves(p):
    r=list(p)
    for i in (0,1):
        j=1-i
        yield ('inv',i), tuple(inv(r[i]) if t==i else r[t] for t in (0,1))
        yield ('mul',i), tuple(red(r[i]+r[j]) if t==i else r[t] for t in (0,1))
        yield ('mulinv',i), tuple(red(r[i]+inv(r[j])) if t==i else r[t] for t in (0,1))
        for g in (1,-1,2,-2):
            yield ('conj',i,g), tuple(red((g,)+r[i]+(-g,)) if t==i else r[t] for t in (0,1))
def search(p0,maxn=2_000_000,maxlen=24):
    p0=tuple(red(w) for w in p0)
    seen={p0:None}; pq=[(sum(map(len,p0)),0,p0)]; c=0
    while pq:
        L,_,p=heapq.heappop(pq)
        if L==2 and sorted(map(len,p))==[1,1]: 
            path=[]; q=p
            while seen[q]: m,q0=seen[q]; path.append((m,q0,q)); q=q0
            return p,path[::-1]
        for m,q in moves(p):
            if q in seen: continue
            lq=sum(map(len,q))
            if max(map(len,q))>maxlen: continue
            seen[q]=(m,p); c+=1; heapq.heappush(pq,(lq,c,q))
        if len(seen)>maxn: return None
    return None
def MS(n,w): return [(-1,)+(2,)*n+(1,)+(-2,)*(n+1), red((1,)+inv(w))]
def wk(k): return red(((-2,) if k>0 else (2,))*abs(k)+(-1,2,1,2))
for k in map(int,sys.argv[1:]):
    r=search(MS(2,wk(k)))
    print(k, None if r is None else (r[0],len(r[1])), flush=True)
