import sys
n=int(sys.argv[1]); ws=sys.argv[2]; name=sys.argv[3]; sys.argv=[sys.argv[0]]
from greedy import *
P={'x':1,'X':-1,'y':2,'Y':-2}
w=tuple(P[c] for c in ws)
p0=tuple(red(x) for x in MS(n,w))
end,path=search(MS(n,w),maxn=800000,maxlen=30)
L={1:'gx',-1:'gx⁻¹',2:'gy',-2:'gy⁻¹'}
def W(w): return '(1 : Word 2)' if not w else '('+' * '.join(L[a] for a in w)+')'
def Pp(p): return '![%s, %s]'%(W(p[0]),W(p[1]))
out=[f"theorem {name}_path : Reachable {Pp(p0)} {Pp(end)} := by"]
names=[]
for idx,(m,a,b) in enumerate(path):
    i=m[1]; j=1-i
    if m[0]=='inv': lem=f"reach_inv {Pp(a)} {i}"
    elif m[0]=='mul': lem=f"reach_mulRight {Pp(a)} (i := {i}) (j := {j}) (by decide)"
    elif m[0]=='mulinv': lem=f"reach_mulRight_inv {Pp(a)} (i := {i}) (j := {j}) (by decide)"
    else: lem=f"reach_conj {Pp(a)} {i} {L[m[2]]}"
    out.append(f"  have s{idx} : Reachable {Pp(a)} {Pp(b)} := reach_of_eq ({lem}) (by apply fin2_ext <;> step_tac)")
    names.append(f"s{idx}")
# finish to standard: end is ((g1^±),(g2^±)) possibly swapped
e0,e1=end
fin=[]
cur=Pp(end)
out.append(f"  have fin : Reachable {Pp(end)} (standard 2) := by")
out.append(f"    first")
out.append(f"    | exact Relation.ReflTransGen.refl")
out.append(f"    | exact reach_of_eq (reach_inv {Pp(end)} 0) (by apply fin2_ext <;> simp [standard])")
out.append(f"    | exact reach_of_eq (reach_inv {Pp(end)} 1) (by apply fin2_ext <;> simp [standard])")
out.append(f"    | exact (reach_inv {Pp(end)} 0).trans' (reach_of_eq (reach_inv _ 1) (by apply fin2_ext <;> simp [standard]))")
out.append(f"    | exact (reach_perm {Pp(end)} (Equiv.swap 0 1)).trans' (by first | exact reach_of_eq Relation.ReflTransGen.refl (by apply fin2_ext <;> simp [standard]) | exact reach_of_eq (reach_inv _ 0) (by apply fin2_ext <;> simp [standard]) | exact reach_of_eq (reach_inv _ 1) (by apply fin2_ext <;> simp [standard]) | exact (reach_inv _ 0).trans' (reach_of_eq (reach_inv _ 1) (by apply fin2_ext <;> simp [standard])))")
chain="fin"
for x in reversed(names): chain=f"{x}.trans' ({chain})"
out.append(f"  exact {chain}")
print("\n".join(out))
print(f"-- start {Pp(p0)}  end {end}")
