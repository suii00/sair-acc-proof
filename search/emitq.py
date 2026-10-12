import sys
q=int(sys.argv[1]); sys.argv=[sys.argv[0]]
from greedy import *
def Y(a): return ((2,) if a>0 else (-2,))*abs(a)
w=red((-2,1)+Y(1-q)+(-1,))
p0=tuple(red(x) for x in MS(2,w))
end,path=search(MS(2,w),maxn=600000,maxlen=30)
L={1:'gx',-1:'gx⁻¹',2:'gy',-2:'gy⁻¹'}
def W(w): return '(1 : Word 2)' if not w else '('+' * '.join(L[a] for a in w)+')'
def P(p): return '![%s, %s]'%(W(p[0]),W(p[1]))
nm=f"v{q}".replace('-','m')
out=[f"theorem MS2_{nm}_path : Reachable {P(p0)} {P(end)} := by"]
names=[]
for idx,(m,a,b) in enumerate(path):
    i=m[1]; j=1-i
    if m[0]=='inv': lem=f"reach_inv {P(a)} {i}"
    elif m[0]=='mul': lem=f"reach_mulRight {P(a)} (i := {i}) (j := {j}) (by decide)"
    elif m[0]=='mulinv': lem=f"reach_mulRight_inv {P(a)} (i := {i}) (j := {j}) (by decide)"
    else: lem=f"reach_conj {P(a)} {i} {L[m[2]]}"
    out.append(f"  have s{idx} : Reachable {P(a)} {P(b)} := reach_of_eq ({lem}) (by apply fin2_ext <;> step_tac)")
    names.append(f"s{idx}")
chain=names[-1]
for x in reversed(names[:-1]): chain=f"{x}.trans' ({chain})"
out.append(f"  exact {chain}")
out.append(f"-- start {P(p0)} end {end}")
print("\n".join(out))
