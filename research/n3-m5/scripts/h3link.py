# H3 link: is x y^a x Y^5 X y^5 (n=3, any a) G-conjugate (G = BS(3,4)) to r1 of a quickly-solved (a',b',c')?
# A hit plus the automorphism transfer x -> y^j x y^k would give a proof (to be certified in Lean). Experiment.
import itertools,sys
from bs import trivial, W
from cyc import red
def yp(k): return 'y'*k if k>=0 else 'Y'*(-k)
def inv(s): return ''.join(c.swapcase() for c in reversed(s))
L=int(sys.argv[1]); A=int(sys.argv[2])
sol=[l.split() for l in open('h3scan.out') if 'SOLVED' in l]
tg=[red('x'+yp(int(a))+'x'+yp(int(b))+'X'+yp(int(c))) for a,b,c,*_ in sol if (int(b),int(c))!=(-5,5)]
gs=['']
for l in range(1,L+1):
    for t in itertools.product('xXyY',repeat=l):
        s=''.join(t)
        if all(s[i]!=s[i+1].swapcase() for i in range(l-1)): gs.append(s)
hits=0
for a in range(-A,A+1):
    src=red('x'+yp(a)+'xYYYYYXyyyyy')
    for t in tg:
        for tt in (t,inv(t)):
            for g in gs:
                if trivial(W(g+src+inv(g)+inv(tt)),3):
                    print('HIT a',a,'src',src,'~',tt,'conj',g,flush=True); hits+=1; break
print('done hits',hits)
