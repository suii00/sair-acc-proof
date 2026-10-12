import sys
n,m=int(sys.argv[1]),int(sys.argv[2]); A=sys.argv[:]; sys.argv=[sys.argv[0]]
from greedy import *
S={1:'x',-1:'X',2:'y',-2:'Y'}
def s(w): return ''.join(S[a] for a in w) or '1'
w=red((-2,)*m+(1,)+(2,)*m+(-1,))
r=search(MS(n,w),maxn=int(A[3]) if len(A)>3 else 400000,maxlen=int(A[4]) if len(A)>4 else 24)
print(s(MS(n,w)[0]),s(red(MS(n,w)[1])))
for mv,a,b in r[1]: print(mv, s(b[0]),'|',s(b[1]))
