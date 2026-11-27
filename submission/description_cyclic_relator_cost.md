# Cyclic rotation can change the minimum Andrews–Curtis conjugation count by rank minus one

For an ordered, trivializable tuple of $n$ relators in the free group of rank $n\ge1$, changing where the relators start can change the minimum number of conjugations needed for trivialization by at most $n-1$. This bound is sharp. In every rank, one fixed ordered tuple of positive cyclic words realizes every minimum $0,1,\ldots,n-1$ by moving the first letter of selected rows to the end. The same assertions hold with stabilization.

For instance, $(yxyxy,yxy)$ has minimum zero and $(yxyxy,xyy)$ has minimum one.

Let $c(R)$ be the minimum number of single-row conjugations $r_i\mapsto gr_i g^{-1}$ in a path from a trivializable ordered tuple $R$ in $F(x_1,\ldots,x_n)$ to $(x_1,\ldots,x_n)$. The conjugator is any free word. Row inversion and right multiplication by another row have zero cost. For $c_{\rm st}$, insertion and deletion of an isolated generator and its singleton relator also have zero cost.

### The upper bound

Simultaneously conjugate an entire ordinary path by $g$. It uses the same number of conjugations and ends at a free basis, which Nielsen operations take to the ordered standard basis at zero cost. Explicitly, conjugation by a basis letter fixes that row and left- and right-multiplies each other row by that letter and its inverse. Left multiplication and division are available using inversions and positive right multiplication. Applying the argument with $g^{-1}$ proves that simultaneous conjugation preserves $c$. If $R'$ conjugates each row of $R$ by its own $g_i$, first compare with the simultaneous conjugate by $g_1$. Only the remaining $n-1$ rows need individual conjugations. These moves are reversible, so $|c(R')-c(R)|\le n-1$. A rotation $uv\mapsto vu$ is conjugation by $u^{-1}$.

For a stable path, give each inserted generator a fresh name, even on reinsertion. Add all these isolated pairs at the start. Leave each row idle until scheduled for insertion and again after scheduled deletion. This lifts the path to fixed rank with the same conjugation count. Its endpoint consists of the final basis and the retired singleton rows, together a basis of the enlarged free group. Apply the automorphism that conjugates the original generators by $g$ and fixes the fresh ones. Restore the ordered basis by Nielsen operations and delete the added pairs. This proves the same bound for $c_{\rm st}$, even when the path deletes an original generator. Ivanov uses the stabilization rearrangement in the proof of Theorem 4.1(a). [Ivanov](https://arxiv.org/pdf/1606.08196#page=12)

### Sharpness at every rank

Take a sign character $\epsilon:F_n\to\{1,-1\}$. Over $\mathbf F_3$, define the signed Fox derivative by $d(x_j)=e_j$ and $d(uv)=d(u)+\epsilon(u)d(v)$. The inverse formula $d(u^{-1})=-\epsilon(u)d(u)$ ensures compatibility with free reduction. Form $J(R)$ with rows $d(r_i)$. Inversion scales a row by a unit, and right multiplication adds a signed multiple of another row. A conjugation changes only one row, so rank can increase by at most one. An isolated insertion adds a row and a column forming a $1$-by-$1$ identity block, preserving corank. Equivalently, on the fixed-rank lift above, extend $\epsilon$ arbitrarily to the fresh generators. Since the standard basis has full rank,

$$
c_{\rm st}(R)\ \ge\ n-\operatorname{rank}_{\mathbf F_3}J(R).
$$

Set $a_1=x_1$. For $i=2,\ldots,n$, write $z=x_i$, $a=a_{i-1}$, and define $b_i=zaz$, $a_i=zazaz$. Start with $(a_n,b_2,\ldots,b_n)$. Choose $S\subseteq\{2,\ldots,n\}$ and rotate precisely the selected $b_i$ to $az^2$. Write $R_S$ for the result.

Conjugating each rotated row by $z$ restores it. The unrotated tuple reduces to the standard basis for free. For $b=zaz$, $v=zazaz$, successively obtain $u=b^{-1}v=az$, $bu^{-1}=z$, and $uz^{-1}=a$ by Nielsen operations on the two rows. Apply this reduction in descending order of $i$.

Now give every generator sign $-1$. All $a_i$ have odd length, so induction gives $d(a_i)=3e_i-2d(a_{i-1})=e_1$, $d(b_i)=2e_i-e_1$, and $d(az^2)=e_1$. The row space has basis $e_1$ together with $2e_i-e_1$ for unrotated indices $i\ge2$. Its corank is $|S|$, proving

$$
c_{\rm st}(R_S)=c(R_S)=|S|.
$$

### A Miller–Schupp example

Write $X=x^{-1}$, $Y=y^{-1}$. The pair $(\mathtt{XyxYY},\mathtt{xxYXy})$ has ordinary minimum three. Move the prefix $\mathtt{Xy}$ to the end of the first row, obtaining $\mathtt{xYYXy}$. This single conjugation gives a lower bound of two for the rotated pair. The following nine moves reach $(x,y)$ with exactly two conjugations. The indices are zero-based, and $M_i$ right-multiplies row $i$ by the other row. [ACC-P000036](https://competition.sair.foundation/contributor-network/acc/ACC-P000036)

~~~text
I₀, M₁, I₀, C₁(YX), M₀, I₀, C₁(Xy), M₁, I₀
~~~

For this particular example, $\epsilon(x)=1,\epsilon(y)=-1$ gives signed derivative rows $(0,1),(3,0)$ before reduction modulo three. Thus $1\le c_{\rm st}\le2$.

Alexander Keur (P12) and Alex Zarco (P28) identify cyclic rotations in length-bounded searches. The theorem here compares distances to the standard basis as the initial representatives vary. Sergei V. Ivanov established the qualitative equivalence of the ordinary and cyclic conjectures. [ACC-P000012](https://competition.sair.foundation/contributor-network/acc/ACC-P000012) · [ACC-P000028](https://competition.sair.foundation/contributor-network/acc/ACC-P000028) · [Ivanov, Corollary 1.3](https://arxiv.org/abs/1606.08196)

The proof above covers all ranks. Running `python3 research/cyclic-relator-cost/check_cuts.py --max-rank 9` checks all 511 constructed choices through rank nine against both the matrix lower bound and the free-word path. Lean 4.29.1 verifies both the rotation undo and the seven-move, zero-conjugation two-row recovery at arbitrary rank in `AC.CyclicRelator.undoRotation` and `AC.CyclicRelator.recoverRows`. It also verifies the Miller–Schupp ordinary minimum in `AC.msStarOneRotated_exact` and the nine-move witness in `AC.msStarOneRotated_witness`.

Codex assisted with the proofs, formal certificates and verification code. Fable 5.2 reviewed the distinction between arbitrary conjugation and rotation of cyclically reduced words. Kimi K3.1 Pro and six Ultramath reviewers on Open Math OS checked the endpoint comparison, the stable argument, and the explicit examples. The all-rank sharpness and stable lower bound are given by the mathematical proof above.
