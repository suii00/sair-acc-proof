# What finite and metabelian evaluations miss about Andrews–Curtis multiplication cost

Work in the free group on $x,y$, with $X=x^{-1}$, $Y=y^{-1}$ and $[s,t]=sts^{-1}t^{-1}$. Count one multiplication when a relator row is right-multiplied by a distinct row. Inversions and conjugations are free in this count. A stable path may also freely insert a fresh generator together with its one-letter relator, or undo such an insertion. The target is the ordered basis pair $(x,y)$. A marking of a group $G$ assigns any two elements to $x,y$.

Let $F_1=F_2=1$ be the Fibonacci numbers. For $L\geq1$, put

$$
c=[x,y],\quad d=Xcx,\quad w=[c,d],\qquad
P_L=(x,yc^L),\quad Q_L=(x,yw^L).
$$

Both pairs are AC-trivializable in rank two. For either pair, a stable trivialization with $m$ multiplications satisfies $L\le F_{m+2}$. Every metabelian marking sends $Q_L$ to the standard pair. Its ordinary multiplication cost is at most $2L+2$, and at $L=1$ both the ordinary and stable minima are exactly two. The proofs below also characterize the classes of groups in which matching every marked evaluation can hide unbounded stable cost. [Submission manuscript](../../submission/description_metabelian_multiplication_cost.md)

### Elementary lower bounds

A direct cyclic-word count gives

$$
  L-1\leq 2(F_{m+2}-1)\quad\text{for }P_L,\qquad
  L\leq 2(F_{m+2}-1)\quad\text{for }Q_L.
$$

For any $B\geq1$, if $\operatorname{lcm}(1,\ldots,B)\mid L$, both pairs evaluate exactly to the target under every marking of every group of order at most $B$. Indeed the orders of the images of $c,w$ divide the order of the group. In fact, every permutation of degree at most $B$ has order dividing that same least common multiple, irrespective of the order of the permutation group. Hence both pairs agree with the target in every such marked action as well. Moreover $c,d$ belong to the commutator subgroup, so $w$ evaluates to the identity in every metabelian group, including infinite ones, for every $L$. Both pairs have identity exponent-sum matrix. Taking $L=k!$ gives pairs with multiplication cost tending to infinity while each fixed finite marked group eventually sees the target exactly.

### Trivializations

Write $a=x,\ b=yxY$. Then $c=ab^{-1}$. To remove one $c$ from $P_L$, conjugate the first row by $y$ to obtain $b$, multiply the second row by it, conjugate the first row back, invert it, multiply the second row by it, and invert the first row once more. This appends $b a^{-1}=c^{-1}$, restores $a$, and uses six moves.

Free reduction gives $d=yXYx$ and $w=\mathtt{xyXXYxyxYXXyxY}=ab^{-2}ab a^{-2}b$. Hence $w^{-1}=b^{-1}a^2b^{-1}a^{-1}b^2a^{-1}$. To remove one $w$ from $Q_L$, append these eight factors to the second row. Keep the first row equal to the factor being appended. Changing its underlying letter between $a,b$ takes one conjugation by $y$ or $Y$, and changing sign takes one inversion. Returning the first row to $a$ gives eight multiplications, six conjugations, and six inversions per block.

### A cyclic count with defect two

On a freely reduced word define $f=\#(xy)-\#(YX)$, counting adjacent letters. Let $\phi(g)$ be the corresponding count around a cyclically reduced representative, with the closing adjacency included. The empty word has count zero. Rotating a cyclic word preserves the count and inversion negates it. Thus $\phi$ is conjugacy invariant and $\phi(g^{-1})=-\phi(g)$. In particular $\phi(x)=\phi(y)=0$.

We first show $|f(gh)-f(g)-f(h)|\leq1$. Use maximal cancellation to write $g=ut,\ h=t^{-1}v$, with $ut,t^{-1}v,uv$ all reduced. The counts internal to $t,t^{-1}$ cancel. If $u,t,v$ are nonempty, set $A=(\operatorname{last}u)^{-1},\, B=\operatorname{first}t,\, C=\operatorname{first}v$. Reduction makes these three directions pairwise distinct. The three possibly contributing seams are $A^{-1}C,A^{-1}B,B^{-1}C$. A seam $p^{-1}q$ has nonzero count only when $\{p,q\}=\{X,y\}$, so at most one seam contributes. If any of $u,t,v$ is empty, at most one seam exists. This proves the bound.

Writing $g=srs^{-1}$ with $r$ cyclically reduced shows $f(g^k)/k\to\phi(g)$, by counting the junctions between copies of $r$. The preceding inequality applied repeatedly to $g^k$ gives $|f(g)-\phi(g)|\leq1$. To bound the defect after homogenization, expand

$$
(gh)^k=g^k(g^{-(k-1)}hg^{k-1})\cdots(g^{-1}hg)h.
$$

Combining these factors costs at most $k$ in the raw count. Each of the $k$ conjugates of $h$ has raw count within one of $\phi(h)$. Divide by $k$ and take the limit to obtain $|\phi(gh)-\phi(g)-\phi(h)|\leq2$.

For $P_L$, cyclic reduction of $yc^L$ gives $y(XYxy)^{L-1}$ and hence $\phi(yc^L)=L-1$. For $Q_L$, the displayed word $w$ has two $xy$'s and one $YX$. It begins with $x$ and ends with $xY$. Inter-block junctions $Yx$ contribute zero. Cyclic reduction of $yw^L$ removes its initial $y$ and final $Y$, and the resulting closing $xx$ contributes zero. Thus $\phi(yw^L)=L$.

### Why stabilization preserves the lower bound

For an intermediate basis $S$, set

$$
\nu_S(g)=\max_{\sigma:S\to\{1,x,y\}} |\phi(\sigma(g))|,
$$

where each assignment extends multiplicatively to the free group on $S$. Every basis generator has value zero. The function is unchanged by conjugation and inversion, and $\nu_S(gh)\leq\nu_S(g)+\nu_S(h)+2$. An injective reindexing into a larger basis preserves the value on old words, since every old assignment extends and every new assignment restricts. The new generator row has value zero. The reverse statement handles destabilization.

Read any trivialization backwards, starting at the basis pair. Give each row weight $\nu+2$, padding the list with virtual weights 2 when fewer than two rows are present. Initially the two largest weights are 2 and 2. Under a multiplication or its inverse (right division), the affected weight is at most the sum of its old weight and that of the distinct helper. The second-largest weight after the move is at most the old largest. Zero-cost moves preserve these bounds, including insertion or removal of a row of weight 2. Induction shows the second-largest and largest weights after $m$ multiplications are at most $2F_{m+1}$ and $2F_{m+2}$, respectively. At the terminal rank-two pair the identity assignment gives $\nu\geq|\phi|$. This proves both inequalities.

### Examples and relation to prior work

| Maximum group order $B$ | $L=\operatorname{lcm}(1,\ldots,B)$ | Lower bound on multiplications for $P_L$ |
| ---: | ---: | ---: |
| 6 | 60 | 7 |
| 10 | 2,520 | 15 |
| 20 | 232,792,560 | 39 |

Borovik, Lubotzky and Myasnikov identify the connected components of finite Andrews–Curtis graphs. Here the two *evaluated tuples coincide*, even though multiplication cost upstairs is unbounded. Bridson already uses Fibonacci growth of products of conjugates to bound AC complexity using filling area, including a stable form. The cyclic word count above is a homogeneous counting quasimorphism. Its application gives elementary bounds for two explicit rank-two families with simultaneous evaluation constraints. [Borovik–Lubotzky–Myasnikov](https://arxiv.org/abs/1103.1295) · [Bridson, Lemma 2.7 and Proposition 2.8](https://arxiv.org/pdf/1504.04187#page=10) · [Calegari–Walker, §5.1](https://nyjm.albany.edu/j/2011/17-31p.pdf#page=21)

Run `python3 research/finite-probe-cost/check.py` from the repository root. The script checks both descent traces and cyclic scores through $L=128$, all 2,809 ordered pairs of reduced words of individual length at most three, selected stabilization cases, and all ordered markings in the finite example groups. It also verifies the deletion masks through $L=128$ and replays the resulting ordinary paths through $L=19$. The six base masks and the six-block induction below establish the bound for every $L$.

### A stronger bound from a published defect-one theorem

Let $1\ne u\in[F(x,y),F(x,y)]$ and $T_L=(x,yu^L)$, with $L\ge1$. Every stable trivialization of $T_L$ with $m$ right multiplications satisfies

$$
L\le F_{m+2}.
$$

For a free basis $S$, write $N_S(g)$ for the smallest number of conjugates of signed basis letters whose product is $g$. This is the standard conjugation-invariant word norm. It is subadditive, is unchanged by inversion and conjugation, and equals one on each generator. Inserting a fresh basis letter preserves the norm of every old word. Inclusion gives one inequality; retracting the fresh letter to the identity in a shortest factorization gives the reverse. Thus the two-largest-weights argument above applies to $N$ itself, with initial largest weights $1,1$. At every rank include two auxiliary weights equal to one when taking maxima. Inserting a weight-one row leaves these maxima unchanged; deleting such a row cannot increase them. Each reverse multiplication replaces one weight by at most its sum with the distinct helper's weight. Hence $N_{\{x,y\}}(yu^L)\le F_{m+2}$. [Brandenbursky, Gal, Kędra and Marcinkowski, cancellation norm](https://arxiv.org/abs/1310.2921) · [Bridson, Lemma 2.7](https://arxiv.org/pdf/1504.04187#page=10)

Regard $F(x,y)$ as the right-angled Artin group on two nonadjacent vertices. The element $u$ is nontrivial with zero abelianization, so it is not conjugate into a subgroup generated by a clique. Heuer's Theorem 7.2 supplies a homogeneous quasimorphism $h$ vanishing on $x,y$, of defect at most one, with $h(u)\ge1$. Thus $h(yu^L)\ge L-1$. On a product of $j\ge1$ conjugates of signed basis letters, $|h|$ is at most $j-1$. Since $yu^L$ has $y$-exponent one, its norm is positive and is at least $L$. Combining the inequalities proves the bound. For $L=60,2520,232792560$ this improves the certified lower bounds to **9, 16, 40** respectively for both explicit families. [Heuer, Theorem 7.2](https://arxiv.org/pdf/1802.01107#page=30)

For the explicit metabelian law $w=[c,d]$, the ordinary upper bound also improves to **$4L$ multiplications**. With $c=ab^{-1}$ as above,

$$
w^{-1}=d c d^{-1}c^{-1}
 =(d a d^{-1})(d b^{-1}d^{-1})\,b\,a^{-1}.
$$

All four factors are conjugates of $x$ or $x^{-1}$. Use the first row successively as each factor, multiply the second row on the right each time, and restore the first row to $x$. The four-multiplication replay in the checker removes one block for every tested $1\le L\le128$. The displayed factorization proves it for every $L$.

**At $L=1$ the minimum is exactly two**, both ordinarily and stably. Put $p=yx$, $q=yXYx$. Direct free reduction gives

$$
yw=(pyp^{-1})\,(qyxYq^{-1})\,(qXq^{-1}).
$$

Starting at $Q_1$, use the first row to multiply the second on the right first by $qxq^{-1}$, then by $(qy)X(qy)^{-1}$. The surviving second row is $pyp^{-1}$. Conjugations and inversions restore both rows to the ordered standard pair. The checker replays this in the positive right-multiplication convention. Lean 4.29.1 separately checks the ordered endpoint and the two multiplications in theorem `AC.MetabelianProbe.first_witness`. [Lean certificate](../../lean/ACProof/MetabelianTwo.lean)

For the matching stable lower bound, give each row its exponent vector over $\mathbf F_2$. The standard and $Q_L$ endpoint matrices are identity matrices. In a fixed-rank path padded with all auxiliary isolated pairs, the two matrices can differ by permutation of their rows or columns. Starting backwards from the basis, exactly one right multiplication creates a row with two nonzero entries, and inversions and conjugations preserve the matrix. Hence one multiplication is impossible. With zero multiplications every row remains conjugate to a signed generator. The cyclic count of $yw^L$ is $L>0$ while every signed generator has count zero, including after projection of padding letters to the identity. Thus every $Q_L$ requires at least two stable multiplications.

### A batched ordinary path with at most $2L+2$ multiplications

Write $W=aBBabAAb$ in the auxiliary alphabet $a=x,\ b=yxy^{-1}$, with capitals for inverses. This is the eight-letter expression for $w$. Deleting $k$ letters from $W^L$ and freely reducing the remaining word to the identity expresses $w^L$ as a product of $k$ conjugates of signed $a,b$. In fact, when deleting a letter $\ell$ from a prefix whose retained part is $p$, record the factor $p\ell p^{-1}$. The factors in scan order followed by the final retained word multiply to the original word. Since signed $a,b$ are conjugates of $x^{\pm1}$, the inverse factors, in reverse order, give a path from $Q_L$ in $k$ multiplications.

Here is a finite induction certificate giving $k=2L+2$. For $L=1$ the four-factor certificate suffices. For $2\le s\le7$ the six starting patterns in [the checker](check.py) delete exactly $2s+2$ letters and leave the identity. Each retains the same subsequence $h=Babb$ in its first block. For the induction $L\mapsto L+6$, insert five blocks immediately after that first block, and one intact block at the end. In the five inserted blocks use these patterns, with a dot denoting a deletion and each column corresponding to its position in $W$.

~~~text
.BBab.A.    aBBa.AAb    a..a.AAb    a.B.bAAb    .BBab..b
~~~

If $G$ is the concatenation of the retained letters in these five blocks, free reduction gives $hGh^{-1}=W^{-1}$; both sides reduce to the word $BaaBAbbA$. Therefore a previously retained word $hR=1$ becomes $hGRW=W^{-1}hRW=1$. The six additional blocks use exactly twelve additional deletions. Induction from the six base exponents gives the asserted ordinary upper bound for every $L$. This controls the number of multiplications; the conjugating words are unrestricted.

### Which classes of groups can miss arbitrarily large costs?

For a fixed class $\mathcal K$ of groups, the following are equivalent.

1. There are ordinarily trivializable ordered rank-two tuples with arbitrarily large **stable** multiplication cost whose evaluations are exactly the standard marked pair for every marking into every group of $\mathcal K$.
2. There is a nonidentity free word that evaluates to the identity for every substitution in every member of $\mathcal K$.

For necessity, choose one tuple of positive cost. A coordinate differs in the free group from its standard generator; their quotient is a nontrivial two-variable common law. For sufficiency, given a nontrivial common law on finitely many variables, substitute distinct free generators of a free subgroup in $F(x,y)$, for example distinct conjugates $y^jxy^{-j}$. This gives a nontrivial two-variable law $v$. At least one $t\in\{x,y\}$ does not commute with $v$, since the center of $F(x,y)$ is trivial. Put $u=[v,t]$. It is a nontrivial common law in $F'$. In particular it maps to 1 when $x$ is killed, hence it belongs to the normal closure of $x$. Write $u^{-1}$ as a fixed finite product of conjugates of $x^{\pm1}$. The first row of $T_L$ can supply each factor by conjugation and inversion; append it to the second row and restore the first. Repeating this gives an ordinary trivialization. All markings into $\mathcal K$ give the standard tuple for every $L$, while $L\le F_{m+2}$ forces unbounded stable multiplication cost. This characterizes **literal equality at every marking**. The finite tests with increasing degree bound use a different tuple for each bound; the class of all finite groups has no common nontrivial law because free groups are residually finite.
