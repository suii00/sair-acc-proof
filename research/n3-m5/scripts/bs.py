# Word problem in BS(n,n+1) = <x,y | x^-1 y^n x = y^(n+1)> via Britton pinches; search G-conjugacy links
# between r1(m) = x x y^-m x^-1 y^m for different m (each link gives an AC-equivalence of MS(n,wA m) presentations).
import sys, itertools
def trivial(word,n):
    st=[]
    def push(g,e):
        if e==0: return
        if st and st[-1][0]==g:
            st[-1][1]+=e
            if st[-1][1]==0: st.pop()
            return
        st.append([g,e])
    for g,e in word:
        if g=='y': push('y',e); continue
        step=1 if e>0 else -1
        for _ in range(abs(e)):
            if len(st)>=2 and st[-1][0]=='y' and st[-2][0]=='x':
                s=1 if st[-2][1]>0 else -1
                a=st[-1][1]
                if s==-1 and step==1 and a%n==0:
                    st.pop(); st[-1][1]+=1
                    if st[-1][1]==0: st.pop()
                    push('y',a//n*(n+1)); continue
                if s==1 and step==-1 and a%(n+1)==0:
                    st.pop(); st[-1][1]-=1
                    if st[-1][1]==0: st.pop()
                    push('y',a//(n+1)*n); continue
            push('x',step)
    return not st
def W(s): return [(c.lower(), 1 if c.islower() else -1) for c in s]
def ypow(k): return 'y'*k if k>=0 else 'Y'*(-k)
def r1(m): return 'xx'+ypow(-m)+'X'+ypow(m)
def inv(s): return ''.join(c.swapcase() for c in reversed(s))
if __name__=='__main__':
    n=int(sys.argv[1]); N=n*(n+1); L=int(sys.argv[2]); M=int(sys.argv[3])
    gs=['']
    for l in range(1,L+1):
        for t in itertools.product('xXyY',repeat=l):
            s=''.join(t)
            if any(s[i]==s[i+1].swapcase() for i in range(l-1)): continue
            gs.append(s)
    for m in (list(map(int,sys.argv[4:])) or range(N)):
      for mp in range(-M,M+1):
        if (mp-m)%N==0: continue
        for sg in (1,-1):
          t=r1(mp) if sg==1 else inv(r1(mp))
          for g in gs:
            if trivial(W(g+r1(m)+inv(g)+inv(t)),n):
              print(m,'~',mp,'(res',mp%N,') sign',sg,'conj',g,flush=True); break
