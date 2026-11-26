## Claim

This partial result toward the ordinary Andrews–Curtis conjecture gives an AC path from an infinite family of Miller–Schupp presentations to the corresponding Akbulut–Kirby presentations. It also gives Lean certificates of AC-triviality for 18 of the 30 residue classes at $n=5$. Both results concern ordinary relator moves at fixed rank two.

Write $P_{n,m}=\mathrm{MS}(n,w_A(m))$, where $w_A(m)=y^{-m}xy^m x^{-1}$. The ordered relators of $\mathrm{MS}(n,w)$ are $(x^{-1}y^nxy^{-(n+1)},\,xw^{-1})$. The relators of $\mathrm{AK}(n)$ express $x^n=y^{n+1}$ and $xyx=yxy$, in that order. Write $P\leadsto Q$ for an ordinary AC path in the official Lean relation `AC.Reachable`, and $T(P)$ for $P\leadsto (x,y)$.

## A path to AK(n)

For every nonnegative integer $n$ and every $t\in\mathbb Z$, put $N=n(n+1)$. We obtain

$$P_{n,-(2n+1)+tN}\leadsto\mathrm{AK}(n).$$

For **either** sign, $T(P_{n,\pm(2n+1)+tN})\iff T(\mathrm{AK}(n))$. On the negative branch the construction gives the path displayed above. The positive branch uses the automorphism $y\mapsto y^{-1}$ to transfer AC-triviality in both directions. The declarations are `MS_wA_reach_AK`, `MS_wA_period_reach_AK` and `MS_wA_pm_iff_AK` in `lean/ACProof/AKFamily.lean`.

**Proof.** The reduction `MS_wA_reduce` takes $m=qn+j$ to the word $y^{-j}xy^{j-q}x^{-1}$ in an AC-equivalent presentation. For $(q,j)=(-2,-1)$, the word is $yxyx^{-1}$ for every $n$. The second relator is therefore $x^2y^{-1}x^{-1}y^{-1}$. Conjugating it by $x^{-1}$ gives $xy^{-1}x^{-1}y^{-1}x=xw_0^{-1}$, where $w_k=y^{-k}x^{-1}yxy$. We now follow the path from $\mathrm{MS}(n,w_0)$ to $\mathrm{MS}(n,w_1)$, and reverse the known path from $\mathrm{AK}(n)$ to $\mathrm{MS}(n,w_1)$. The period theorem `MS_wA_period_mul` extends this construction to every translate. Shehper et al. prove the first of these two paths for $n>0$. Myasnikov, Myasnikov and Shpilrain prove the second for $n\ge2$. Our Lean lemmas apply to both steps at every nonnegative integer $n$, including $0$ and $1$. [Shehper et al., Thm. 6](https://arxiv.org/html/2408.15332v2#S3.SS5) · [Myasnikov, Myasnikov and Shpilrain, Prop. 1.3](https://arxiv.org/abs/math/0302080)

For example, $P_{3,5}\leadsto\mathrm{AK}(3)$ since $5=-7+12$, and $P_{4,-9}\leadsto\mathrm{AK}(4)$. At $n=5$ the period is 30. Every $m\equiv19\pmod{30}$ gives a path to $\mathrm{AK}(5)$, since $19\equiv-11$. For $m\equiv11$ or $19\pmod{30}$, triviality is equivalent to that of $\mathrm{AK}(5)$ (`MS5_wA_19_reach_AK5`, `MS5_wA_11_19_iff_AK5`). The AC-triviality of $\mathrm{AK}(5)$ remains unresolved here.

## Unconditional trivializations at n = 5

`MS5_wA` proves $T(P_{5,m})$ for **18 residue classes modulo 30**, independently of $\mathrm{AK}(5)$.

| Source of the Lean proof | Residues of $m$ modulo 30 |
|---|---|
| The divisibility and $\pm1$ families from the preceding version (12 classes) | $0,1,5,6,10,12,15,18,20,24,25,29$ |
| Six search certificates, extended by the period theorem | $2,3,27,28,9,21$, respectively represented by $2,3,-3,-2,-21,-9$ |

Each certificate gives a path from a reduced representative to $(x,y)$. `MS_wA_reduce` connects the original presentation to that representative. The base theorems are `MS5_wA_m2`, `MS5_wA_m3`, `MS5_wA_m27`, `MS5_wA_m28`, `MS5_wA_m9` and `MS5_wA_m21`, in the order above.

**Comparison with the benchmark.** Fagan et al., Appendix F.1, Table 2, already report triviality for all six reduced representatives. The following table specifies the rows in their $n=5$ column. For a reduced word $y^a x y^b x^{-1}$, the second relator is $x^2y^{-b}x^{-1}y^{-a}$. Moving its initial $x$ to its end is an AC conjugation and gives the second relator for the alternative word $x^{-1}y^a x y^b$. This accounts for the rows beginning with $x^{-1}$. [Fagan et al., Table 2](https://arxiv.org/html/2606.21611v1#A6.T2)

| Signed $m$ | Benchmark word $w$ in $\mathrm{MS}(5,w)$ |
|---|---|
| $2$ | $x^{-1}y^{-2}xy^2$ |
| $3$ | $y^2xy^{-3}x^{-1}$ |
| $-3$ | $x^{-1}y^{-2}xy^3$ |
| $-2$ | $y^2xy^{-2}x^{-1}$ |
| $-21$ | $yxy^3x^{-1}$ |
| $-9$ | $x^{-1}y^{-1}xy^3$ |

The same benchmark reports triviality for two more representatives. At $m=4$, the reduction gives $yxy^{-2}x^{-1}$ directly. At $m=-4$, the reduced word $y^{-1}xy^2x^{-1}$ gives the table row $x^{-1}y^{-1}xy^2$ by the conjugation above. With the period theorem these external results account for $m\equiv4,26\pmod{30}$. The count of 18 in `MS5_wA` excludes these two. The pairs $\pm7,\pm8,\pm13,\pm14$ modulo 30 remain undecided by the results presented here. [Fagan et al., Table 2](https://arxiv.org/html/2606.21611v1#A6.T2)

## Earlier results and credit

The preceding submission proves $P_{n,m}\leadsto P_{n,m+tN}$ for all $m,t\in\mathbb Z$, and $T(P_{n,m})$ when $m$ is a multiple of $n$ or $n+1$, or $m=\pm1+tN$. It proves unconditional AC-triviality for all $m$ at $n=2$, for all residues outside $\pm5\bmod 12$ at $n=3$, and for all residues outside $\pm3,\pm7,\pm9\bmod 20$ at $n=4$. It also gives equivalences of AC-triviality with $\mathrm{AK}(3)$ and $\mathrm{AK}(4)$ for the respective classes $\pm5$ and $\pm9$. The $\mathrm{AK}(3)$ connection has earlier descriptions and an explicit certificate. [Iitsuka, ACC-P000018](https://competition.sair.foundation/contributor-network/acc/ACC-P000018) · [Shehper et al.](https://arxiv.org/abs/2408.15332) · [Carreras, Thm. 4](https://arxiv.org/abs/2607.23611)

Sneiderman's ACC-P000002 concerns a square-presentation family. Auxiliary Lean modules in his repository give divisibility, residue and $n=2$ results for a three-parameter family. Our earlier bridge `MS_wA_reach_SnPres` identifies its parameters as $(a,b,c)=(-m,m,0)$. For the negative representative $m=-(2n+1)$, Sneiderman’s `shift_steps` with shift parameter $t=2$ gives an AC path from $(2n+1,-2n-1,0)$ to $(1,1,0)$. The latter has second equation $x^2=yxy$, the equation of $\mathrm{MS}(n,w_0)$. Thus in the common published range $n\ge2$, his shift and the two cited classical paths already imply the path to $\mathrm{AK}(n)$ for this representative. Our Lean proof states the composite directly in $w_A$ coordinates and proves its period and sign consequences. The six $n=5$ certificates independently formalize the benchmark examples above. We claim no priority for these identifications or trivializations. [Sneiderman, ACC-P000002](https://competition.sair.foundation/contributor-network/acc/ACC-P000002) · [Sneiderman, tagged source of `shift_steps`](https://github.com/Robby955/ac-square-divisibility/blob/d0ed2c06bb3a9e7ed31e2f31e24d17de6323efe8/lean/ACParameterShift.lean#L58)

## Reproduction and AI assistance

Run `scripts/reproduce.sh` from the submitted repository. It fetches the pinned official statement, checks its SHA-256, builds `AC` and `ACProof`, and audits the theorems listed in `lean/ACProof/Check.lean` against `propext`, `Classical.choice` and `Quot.sound`. The pinned environment uses Lean 4.29.1 and Mathlib `5e932f97`. [Official AC.lean at the pinned commit](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/lean/AC.lean)

Open Math OS ran the unmodified reproduction script from a clean checkout of proof commit `f2ba667089229bcc4a1c0c0576c407c9ac3794c9`. The build completed, the source scan found no `sorry` or `admit`, and all 71 theorems passed the axiom audit. The run printed `REPRODUCE OK` and exited with status 0. An independent clean macOS run produced the same axiom lists for all 71 declarations. The submission commit adds the manuscript and full log to the audited proof sources. [Manuscript](https://github.com/suii00/sair-acc-proof/blob/ea17200e66b124e8cf042f387e2013056f405690/draft_writeup.md) · [Full Open Math OS log](https://github.com/suii00/sair-acc-proof/blob/ea17200e66b124e8cf042f387e2013056f405690/logs/build_axioms_v1.3.log) · [Audited Lean module](https://github.com/suii00/sair-acc-proof/blob/f2ba667089229bcc4a1c0c0576c407c9ac3794c9/lean/ACProof/AKFamily.lean)

AI assistance contributed to the search, Lean proofs and preparation of the manuscript. Open Math OS provided a Lean verification environment. Claude Fable helped draft the short proof of the uniform path and reviewed the submission.
