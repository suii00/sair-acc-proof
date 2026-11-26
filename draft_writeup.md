# A periodic Miller–Schupp class reaching the Akbulut–Kirby presentation

SAIR Andrews–Curtis Challenge, Proof Track. Partial result, v1.3 submission candidate.

For every $n\in\mathbb N$ and $t\in\mathbb Z$, we give an ordinary AC path from $\mathrm{MS}(n,w_A(m))$ to $\mathrm{AK}(n)$ for $m=-(2n+1)+tn(n+1)$. For $m=\pm(2n+1)+tn(n+1)$ the two presentations have equivalent AC-triviality. At $n=5$ the path concerns class 19 modulo 30. The equivalence of triviality concerns classes 11 and 19. Separately, we certify unconditional AC-triviality for 18 residue classes at $n=5$ by the general families and six independently generated Lean paths.

In the classical range $n\ge2$, the proof identifies the parameter that joins Sneiderman’s shift with the equivalences of Shehper et al. and Myasnikov–Myasnikov–Shpilrain. Fagan et al. already list the six finite benchmark cases as trivial. Our contribution is the uniform statement in the official AC definitions, its Lean proof, and the explicit correspondence between the certified residues and the published table. [Sneiderman, parameter shifts](https://github.com/Robby955/ac-square-divisibility/blob/v0.1.0/lean/ACParameterShift.lean) · [Shehper et al., §3.5](https://arxiv.org/html/2408.15332v2#S3.SS5) · [Myasnikov et al., Prop. 1.3](https://arxiv.org/pdf/math/0302080) · [Fagan et al., Table 2](https://arxiv.org/html/2606.21611v1#A6.T2)

The target is the official `AC.Reachable` relation on ordered tuples, with `AC.standard 2` as the trivial presentation. The reproduction script pins `AC.lean` at commit `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e` and verifies SHA-256 `927ba318d26b06c312140117b2a4856373832ed2c043944f520ec7337bcfca1b`. Open Math OS verified proof commit `f2ba667089229bcc4a1c0c0576c407c9ac3794c9` with Lean 4.29.1 and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. All 71 declarations passed the axiom audit, including the five new statements from Theorem 5. The run ended with `REPRODUCE OK` and exit code 0. [Official definitions](https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/tools/lean/AC.lean) · [v1.3 full build and axiom log](logs/build_axioms_v1.3.log) · [Reproduction script](scripts/reproduce.sh)

## 0. Conventions and terminology
x = `FreeGroup.of 0`, y = `FreeGroup.of 1`, X = x⁻¹, Y = y⁻¹.
`MS n w = ![x⁻¹yⁿx(y^{n+1})⁻¹, x w⁻¹]` = ⟨x,y | x⁻¹yⁿx = y^{n+1}, x = w⟩ (Miller–Schupp).
wA(m) = y^{-m} x y^m x⁻¹; w⋆ = y⁻¹xyx⁻¹ = wA(1); w_k = y^{-k}x⁻¹yxy; v(q) = y⁻¹xy^{1-q}x⁻¹.
AK(n) = ⟨x,y | xⁿ = y^{n+1}, xyx = yxy⟩ (Lean `AK n`).
- **AC-trivial**: `Reachable R (standard 2)`.
- **AC-equivalent presentations** (R ~ S): `Reachable R S`. This relation is symmetric (`Reachable.symm`).
- **AC-triviality transfer** (R ⇒triv S): "R AC-trivial implies S AC-trivial". This gives no AC path. `MS_wA_negate`,
  the shear steps, and the earlier AK(3) and AK(4) iff lemmas are transfers. Theorem 5 gives a path for an entire residue class.
- **Sneiderman coordinates**: `SnPres n a b c = ![x⁻¹yⁿxy^{-(n+1)}, x⁻¹y^a x y^b x⁻¹y^c]` (our restatement, Comparison.lean).
  `MS_wA_reach_SnPres : MS n (wA m) ~ SnPres n (−m) m 0` (one inversion plus one conjugation).
  For $n>0$, CRT identifies m mod n(n+1) with the cell (−m mod n, m mod n+1).

## 1. Results (Lean)
**Theorem 1 (period; all n).** `MS_wA_period`, `MS_wA_period_mul`: MS(n, wA m) ~ MS(n, wA(m + t·n(n+1))).
Corollary `MS_wA_of_residues`.
*Prior art:* the triviality consequence follows from Sneiderman `residue_solvable_iff`, which proves finer independent
periods (n in a, n+1 in b) of the 3-parameter family. Our statement is an AC-equivalence of the two presentations, proved
by one-relator conjugacy (the Panteleev–Ushakov Thm 2.3 mechanism). Sneiderman's a-period passes through a shear
(triviality transfer), so this AC-equivalence form is a minor refinement not found stated. Novelty is not claimed.

**Theorem 2 (n = 2, all integers).** MS(2, wA m) is AC-trivial for every m ∈ ℤ (`MS2_wA_all'`; alternative `MS2_wA_all`).
*Prior art:*
- Implied by Sneiderman `all_parameters_two` (all a, b, c at n = 2) via `MS_wA_reach_SnPres`.
- The instances m = ±1, ±5 (length-12 presentations MS(2, y^{±1}xy^{±1}x⁻¹)) were trivialized by Myasnikov 1999 and
  Havas–Ramsay 2003.
- Benchmark instances also appear as trivial in Shehper et al. and Fagan et al.
Ours is an independent proof.

**Theorem 3 (general families; all n).** `MS_wA_cover`: MS(n, wA m) is AC-trivial whenever m ∈ nℤ ∪ (n+1)ℤ ∪
(±1 + n(n+1)ℤ).
*Prior art:* implied by Sneiderman's `zero_a_solvable`, `zero_b_solvable`, `uniform_family` (the cell (n−1, 1)) and
`YInversion.solution`.

**Theorem 4 (n = 3, 4, 5; certified search paths).** `MS3_wA`: AC-trivial for m mod 12 ∉ {5, 7}. `MS4_wA`: AC-trivial for
m mod 20 ∉ {3, 7, 9, 11, 13, 17}. `MS5_wA`: AC-trivial for m mod 30 ∉ {4, 7, 8, 11, 13, 14, 16, 17, 19, 22, 23, 26}.
At $n=5$, Theorem 3 covers $0,1,5,6,10,12,15,18,20,24,25,29$ modulo 30. Six search certificates cover $2,3,9,21,27,28$. The published benchmark already records each short representative as trivial. Section 2d gives the matching words and the two further literature cases.

**Theorem 5 (uniform AK reduction).** Fix $n\in\mathbb N$, $t\in\mathbb Z$ and put $N=n(n+1)$. For $m=-(2n+1)+tN$, the presentation $\mathrm{MS}(n,w_A(m))$ reaches $\mathrm{AK}(n)$. For $m=\pm(2n+1)+tN$, its AC-triviality is equivalent to that of $\mathrm{AK}(n)$. For $n>0$ these equalities describe residue classes. At $n=0$ they give the path for $m=-1$ and the equivalence of triviality for $m=\pm1$. At $n=5$ the path covers class 19 and the triviality equivalence covers classes 11 and 19.

The underlying parameter step appears in Sneiderman’s `shift_steps` at $t=2$. In coordinates $(a,b,c)=(-m,m,0)$ it carries $(2n+1,-2n-1,0)$ to $(1,1,0)$. The second relation there is $x^2=yxy$. Identify it with $\mathrm{MS}(n,w_0)$. In the published ranges, [SMF, Thm 6] applies for $n>0$ and [MMS, Prop 1.3] for $n\ge2$. Our Lean lemmas prove both steps for every natural $n$. The periodic extension uses the separate path of Theorem 1. At $n=3$ the finite identification also follows from Carreras’s Theorem 4. At $n=5$ Fagan et al. put the words $yxyx^{-1}$ and $yxyx^{-1}y^{-1}$ in class $16_1$. The second relator of the latter is cyclically conjugate to the second relator for $w_1$, giving an independent prior identification of the finite base. [Sneiderman](https://github.com/Robby955/ac-square-divisibility/blob/v0.1.0/lean/ACParameterShift.lean) · [Carreras](https://arxiv.org/html/2607.23611v1) · [Fagan et al., Table 2](https://arxiv.org/html/2606.21611v1#A6.T2)

## 2. Classification of results and theorem ↔ Lean correspondence
Files are under `lean/ACProof/`. See §5 for the sources.

### 2a. Formalization of known results (credit to the original authors)
George and Zhao report an earlier formalization of the results of [SMF] in their own framework (§5b).

| Statement | Lean name | File | Src |
|---|---|---|---|
| AC-moves preserve the normal closure; triviality invariance | `Reachable.ncl_eq` (helper), `Reachable.presentsTrivialGroup_iff`, `Reachable.presentsTrivialGroup` | Basic | standard |
| R ~ S is symmetric; left mult., swap, permutations, endomorphism transport | `Reachable.symm`, `reach_mulLeft`, `reach_swap`, `reach_perm`, `Reachable.map`, `Reachable.relabel` | Basic | standard |
| multiply a relator by any element of the normal closure of another | `reach_mul_normalClosure` | Consequence | standard |
| MS(1, w) AC-trivial ∀w (x-exponent sum 0) | `MS1_reachable` | MS1 | [SMF] Thm 2 |
| MS(n, w⋆) AC-trivial ∀n | `MS_wstar_reachable` | MS1 | [SMF] Thm 3 |
| MS(n, w_k) ~ MS(n, w_{k+1}) and ~ for all k, k' | `MS_wk_succ`, `MS_wk_equiv` | MSwk | [SMF] Thm 6 |
| MS(2, w_k) AC-trivial ∀k | `MS2_wk_reachable` | MS2 | [SMF] Cor 9 (via our own certified 21-move path for w_3) |
| AK(n) ~ MS(n, w_1) | `AK_reach_MS` | AK | [MMS] Prop 1.3; [SMF] Prop 5; George–Zhao `AK_equiv_MS_w₁` |
| AK(2) AC-trivial | `AK2_reachable` | AK | [MMS] Prop 1.1 |
| MS(n, w_k) ~ P(n, k) | `MS_reach_P` | AK | [SMF] Thm 7 |

### 2b. AK reduction and earlier specializations

| Statement | Lean name | File | Status |
|---|---|---|---|
| automorphism φ_k: x ↦ xy^k, y ↦ y, with inverse φ_{−k} | `phiK`, `phiK_inv_comp`, `phiK_comp_MS`, `phiK_std`, `std_of_xyk` (def/helper lemmas, not separately listed in Check.lean; used by the audited theorems) | AK3Link | standard (PU Lemma 3.1) |
| key BS(3,4) identity; φ₃(MS(3,wA 5)) ~ MS(3, w_8) | `link_identity`, `phi_MS3_wA5_reach_wk8` | AK3Link | proof ingredient |
| MS(3, wA 5) triv ⇔ AK(3) triv; AK(3) triv ⇒ all MS(3, wA m) triv | `MS3_wA5_iff_AK3`, `MS3_wA_of_AK3` | AK3Link | KNOWN ([SMF] v2 §3; [Car] Thm 4; [Fag] App. F) |
| BS(4,5) identities; φ₋₆(MS(4,wA(−9))) ~ MS(4, w_{−9}) | `bs_pow`, `link4_identity`, `phi_MS4_wAm9_reach_wkm9` | AK4Link | proof ingredient |
| MS(4, wA(−9)) triv ⇔ AK(4) triv; AK(4) triv ⇒ m ≡ 9, 11 (mod 20) | `MS4_wAm9_iff_AK4`, `MS4_wA_9_11_of_AK4` | AK4Link | also follows from Theorem 5 |
| Path at $m=-(2n+1)$ and its periodic translates | `MS_wA_reach_AK`, `MS_wA_period_reach_AK` | AKFamily | Thm 5 |
| AC-triviality iff AK(n) is AC-trivial for both signs | `MS_wA_pm_iff_AK` | AKFamily | Thm 5 |
| Path to AK(5) for class 19 and triviality iff for 11 or 19 | `MS5_wA_19_reach_AK5`, `MS5_wA_11_19_iff_AK5` | AKFamily | Thm 5 at $n=5$ |

### 2c. Independent proofs of consequences of Sneiderman’s general families

| Statement | Lean name | File | Prior art |
|---|---|---|---|
| correspondence MS(n, wA m) ~ SnPres n (−m) m 0 | `MS_wA_reach_SnPres`, `SnPres_reach_MS_wA` | Comparison | (comparison lemma, ours) |
| MS(n, y^k) AC-trivial | `MS_ypow_reachable` | MillerSchupp | [Sn] `power_second_solvable` |
| m ∈ nℤ; m = ±n, ±(n+1); reduction mod n | `MS_wA_mult`, `MS_wA_neg`, `MS_wA_self`, `MS_wA_succ`, `MS_wA_negsucc`, `MS_wA_reduce`, `MS_wA_diag` | NewFamilies | [Sn] `zero_a_solvable`, `a_period` |
| m ∈ (n+1)ℤ | `MS_wA_mult_succ` | General | [Sn] `zero_b_solvable`, `b_period` |
| m = 1 | `MS_wA_one` | General | [SMF] Thm 3 (w⋆); [Sn] `uniform_family` |
| transfer MS(n, wA(−m)) ⇒triv MS(n, wA m) | `MS_wA_negate` | General | PU Lemma 3.1; [Sn] `YInversion.solution` |
| m ≡ ±1 mod n(n+1) | `MS_wA_neg_one`, `MS_wA_pm_one` | General | [Sn] `uniform_family` + `residue_solvable_iff` |
| Thm 3 | `MS_wA_cover` | General | [Sn] (combination, §5b) |
| Thm 1, period n(n+1) (AC-equivalence form) | `MS_wA_period`, `MS_wA_period_mul`, `MS_wA_of_residues` | Period | triviality consequence: [Sn] `residue_solvable_iff` |
| Thm 2 (n = 2, all m) | `MS2_wA_all'` (proof A), `MS2_wA_all`, `MS2_v_shift`, `MS2_v_reachable` (proof B) | MS2Alt, MS2All | [Sn] `all_parameters_two`; instances m=±1,±5: Myasnikov 1999, Havas–Ramsay 2003 |

### 2d. Certified residue classes and published benchmark words

The $n=3,4$ classifications are `MS3_wA` and `MS4_wA` in `N3.lean` and `N4.lean`. For $n=5$, write $m=5q+j$. The lemma `MS_wA_reduce` reaches the word $u=y^{-j}xy^{j-q}x^{-1}$. For each of the following six certificates, Table 2 of Fagan et al. marks the stated benchmark word $w$ **trivial** in column $n=5$. When $u=y^a x y^b x^{-1}$ and the table gives $w=x^{-1}y^a x y^b$, the second relation words satisfy $xw^{-1}=x^{-1}(xu^{-1})x$. Thus each match preserves ordinary AC reachability with the first relation fixed. [Source certificates](lean/ACProof/N5.lean) · [Fagan et al., Table 2](https://arxiv.org/html/2606.21611v1#A6.T2)

| Residue | Base $m$ | $(q,j)$ | Published row word $w$ | Lean certificate | Search transitions |
|---:|---:|:---:|---|---|---:|
| 2 | 2 | (0, 2) | $x^{-1}y^{-2}xy^2$ | `MS5_wA_m2` | 52 |
| 3 | 3 | (1, −2) | $y^2xy^{-3}x^{-1}$ | `MS5_wA_m3` | 30 |
| 9 | −21 | (−4, −1) | $yxy^3x^{-1}$ | `MS5_wA_m9` | 96 |
| 21 | −9 | (−2, 1) | $x^{-1}y^{-1}xy^3$ | `MS5_wA_m21` | 44 |
| 27 | −3 | (−1, 2) | $x^{-1}y^{-2}xy^3$ | `MS5_wA_m27` | 28 |
| 28 | −2 | (0, −2) | $y^2xy^{-2}x^{-1}$ | `MS5_wA_m28` | 54 |

The counts refer to transitions emitted by the search. A transition multiplying by an inverse relator can expand into several official moves. Each certificate also supplies the initial reduction and a final normalization to the ordered standard pair. Theorem 1 transfers the six cases to every integer in their classes.

**Two further literature cases.** For $m=4$ take $(q,j)=(1,-1)$, giving $yxy^{-2}x^{-1}$. For $m=-4$ take $(-1,1)$, giving $y^{-1}xy^2x^{-1}$, whose second relator is conjugate as above to that of the row $x^{-1}y^{-1}xy^2$. Both published rows are trivial. Theorem 1 extends this paper deduction to classes 4 and 26, outside the 18 covered by the Lean theorem `MS5_wA`. [Fagan et al., Table 2](https://arxiv.org/html/2606.21611v1#A6.T2)

### 2e. Remaining cases

For $n=5$, the AC-triviality of classes 7, 8, 13, 14, 16, 17, 22 and 23 remains undecided by these results. Theorem 5 ties classes 11 and 19 to the open AC-triviality of AK(5). At $n=3$, the remaining classes $\pm5$ have the triviality of AK(3). At $n=4$, the same holds for $\pm9$ and the classification in Theorem 4 leaves $\pm3,\pm7$ undecided. At higher $n$, Theorems 3 and 5 apply in their specified classes. These results leave the general AC conjecture open.

## 3. Paper proofs (human-checkable without Lean)
Let G = F(x,y)/⟨⟨r0⟩⟩, r0 = x⁻¹yⁿxy^{-(n+1)}, K: x⁻¹yⁿx = y^{n+1}; r1(m) = x·wA(m)⁻¹ = x·x y^{-m} x⁻¹ y^m.
AC fact (Lean `reach_slot1_mod`, `reach_slot1_conj`): if the image of r1' in G is conjugate to the image of r1, then
(r0, r1) ~ (r0, r1').

**Proof of Theorem 5.** Put $m=-(2n+1)=-2n-1$. Apply `MS_wA_reduce` with $(q,j)=(-2,-1)$ to reach $\mathrm{MS}(n,yxyx^{-1})$. Its second relator is $r=x^2y^{-1}x^{-1}y^{-1}$. Conjugating by $x^{-1}$ gives $x^{-1}rx=xy^{-1}x^{-1}y^{-1}x=xw_0^{-1}$. The first relator stays fixed. Apply `MS_wk_equiv n 0 1`, then reverse `AK_reach_MS` to reach $\mathrm{AK}(n)$. For each $t\in\mathbb Z$, precompose this chain with the reverse of `MS_wA_period_mul` to start at $m+t n(n+1)$. Applying the sign-transfer lemma in both directions gives the equivalence of triviality on the positive class. [Formal proof](lean/ACProof/AKFamily.lean)

**Theorem 1.**
Step 1 (period). From K: x y^{n+1} x⁻¹ = yⁿ, hence (i) x y^{(n+1)k} x⁻¹ = y^{nk} and (ii) y^{nk} x = x y^{(n+1)k}.
Put N = n(n+1), D_m = x y^{-m} x⁻¹, so r1(m) = x D_m y^m.
 • r1(m+N) = x·D_m·(x y^{-N} x⁻¹)·y^{m+N} = x D_m y^{-n²} y^{m+N} = x D_m y^{m+n}    [by (i), k = -n].
 • y^{n²} r1(m) y^{-n²} = (y^{n²} x) D_m y^{m-n²} = x y^{N} D_m y^{m-n²}             [by (ii), k = n].
   y^N = x y^{(n+1)²} x⁻¹ by (i) (k = n+1); both y^N and D_m are x·(power of y)·x⁻¹, so they commute:
   = x D_m y^{N} y^{m-n²} = x D_m y^{m+n}.
 So r1(m+N) is conjugate to r1(m) in G, and MS(n,wA m) ~ MS(n, wA(m+N)). For n=2, N=6.


**Transfer `MS_wA_negate`.** ψ: x ↦ x, y ↦ y⁻¹ is an automorphism of F. ψ(r0) = x⁻¹y^{-n}xy^{n+1} = (y^{-(n+1)} r0 y^{n+1})⁻¹, so
MS(n, wA m) ~ (ψ(r0), x·wA(m)⁻¹) by one conjugation and one inversion; and ψ(wA(−m)) = wA(m), so this pair is
ψ applied to MS(n, wA(−m)). If MS(n, wA(−m)) ~ (x, y), applying ψ to every move (`Reachable.map`) gives
ψ(MS(n, wA(−m))) ~ (x, y⁻¹) ~ (x, y). This transfers triviality; it does not give an AC path between MS(n, wA m) and
MS(n, wA(−m)).

**Theorem 2, proof A (n = 2, N = 6).** Write m = 6k + r with 0 ≤ r < 6.
- r ∈ {0, 2, 4}: m ∈ 2ℤ. In G, y^{-2q} x y^{2q} = x y^{-q}, so r1 = x·x y^q x⁻¹, conjugate to x y^q. Substitute x = y^{-q}
  into r0 (`subst_reachable`) to get y⁻¹; then (y⁻¹, x y^q) → (x, y).
- r = 3: m ∈ 3ℤ. Reduction mod 2 with j = q turns wA into y^{-q}; same argument (`MS_wA_mult_succ`).
- r = 1: m ∈ 1 + 6ℤ. By Theorem 1, MS(2, wA m) ~ MS(2, wA 1) = MS(2, w⋆), AC-trivial by [SMF] Thm 3.
- r = 5: m ∈ −1 + 6ℤ. By Theorem 1, ~ MS(2, wA(−1)); by the transfer, it is AC-trivial because MS(2, wA 1) is.

## 4. Appendix — proof B of Theorem 2 and the certified search paths
Proof B uses the shift MS(2, v(q)) ~ MS(2, v(q+3)) (BS(2,3) identity: xy³x⁻¹ = y², y⁴x = xy⁶, y⁶ = xy⁹x⁻¹ commutes with
xy^{q-1}x⁻¹), bases q = 0 (w⋆), q = 1 (y⁻¹) and 19 search transitions for q = −1 followed by a final inversion:
 • m = 5 ≡ -1: write -1 = (-1)·2 + 1, reduction mod 2 gives the second relator for v(-1) = y⁻¹ x y² x⁻¹. Explicit path
   (r0, r1) = (Xyy x YYY, xxYYXy) [X = x⁻¹, Y = y⁻¹]; "c_i g" = conjugate relator i by g (g r g⁻¹);
   "i/j" = r_i·r_j⁻¹; "i·j" = r_i·r_j; "inv i"; words reduced cyclically-free only where the move does so:
    0 c0 x → (yyxYYYX, xxYYXy)    1 c0 Y → (yxYYYXy, ·)   2 0/1 → (yxYXX, ·)   3 c0 Y → (xYXXy, ·)   4 c0 X → (YXXyx, ·)
    5 c1 X → (·, xYYXyx)   6 1/0 → (·, xYYxy)   7 c0 y → (XXyxY, ·)   8 c1 X → (·, YYxyx)   9 c1 y → (·, YxyxY)
   10 1/0 → (·, Yxxx)   11 c1 x → (·, xYxx)   12 1·0 → (·, xxY)   13 0/1 → (XXyX, ·)   14 c0 x → (XyXX, ·)
   15 0·1 → (X, ·)   16 inv 1 → (·, yXX)   17 1/0 → (·, yX)   18 1/0 → (X, y), then inv 0 → (x, y).
   Each line can be checked by free reduction by hand (e.g. step 2: yxYYYXy·(xxYYXy)⁻¹ = yxYYYXy·YxyyXX = yxYXX).

The $n=3,4$ paths were generated by greedy search. The Lean proofs replay the transitions as ordinary AC paths and normalize the final generator pair to `standard 2`. [Proof tactics](lean/ACProof/Tactics.lean)

## 5. Sources

| Key | Work | Version checked | Used for |
|---|---|---|---|
| [AC] | J.J. Andrews, M.L. Curtis, Free groups and handlebodies, Proc. AMS 16 (1965) 192–195 | journal | statement of the conjecture |
| [OFF] | SAIRcompetition/Andrews-Curtis, `competition/tools/lean/AC.lean` | commit a0fd6e6f, sha256 927ba318… | official definitions (unchanged) |
| [MiS] | C.F. Miller III, P.E. Schupp, Some presentations of the trivial group, Contemp. Math. 250 (1999) 113–115 | MR1732210 | definition of MS(n, w) |
| [AK] | S. Akbulut, R. Kirby, Topology 24 (1985) 375–390 | journal | definition of AK(n) |
| [MMS] | A.D. Myasnikov, A.G. Myasnikov, V. Shpilrain, On the Andrews–Curtis equivalence, Contemp. Math. 296 (2002) 183–198 | arXiv:math/0302080v1 | Prop 1.1 (AK(2)), Prop 1.3 (AK(n) ~ MS(n, w_1)) |
| [SMF] | A. Shehper, A. Medina-Mardones, et al., S. Gukov, What makes math problems hard for reinforcement learning: a case study | arXiv:2408.15332v2 (11 Feb 2025) | Thm 2, 3, Prop 5, Thm 6, 7, Cor 9; §3 (length-14 MS(3,·) ~ AK(3)) |
| [Car] | J. Carreras, Machine-checkable equivalence certificates at the length-14 Andrews–Curtis frontier | arXiv:2607.23611v1; repo joe-carr-data/ac-certificates @ d347fc47 (Python verifier, no Lean) | Thm 4: MS(3, y⁻¹x²y⁻¹) ~ AK(3) |
| [Fag] | L. Fagan, M. Tarquini, A. Shehper, et al., S. Gukov, The Two-Hump Problem | arXiv:2606.21611v1; repo Math-AI-Caltech/ACSolverX @ 6a12515f (JAX, no Lean) | App. F, Table 2 (six certified $n=5$ cases, $\pm4$ and class $16_1$), plus classes $13_1$ and $15_1$ |
| [PU] | D. Panteleev, A. Ushakov, Conjugacy search problem and the Andrews–Curtis conjecture | arXiv:1609.00325 | Lemma 3.1 (automorphisms preserve AC-triviality), Thm 2.3, Prop 3.7 / Cor 3.8 (standard techniques) |
| [My] / [HR] | A.D. Myasnikov, IJAC 9 (1999) 671–686; G. Havas, C. Ramsay, IJAC 13 (2003) 61–68 | journal (web copy for [HR]) | prior trivializations of MS(2, y^{±1}xy^{±1}x⁻¹), i.e. our m = ±1, ±5 at n = 2 |
| [Sn] | R. Sneiderman, Explicit AC constructions for divisibility subfamilies of square presentations, SAIR ACC-P000002 (https://competition.sair.foundation/contributor-network/acc/ACC-P000002, published 2026-09-13; claim is about G(p,s) only); package github.com/Robby955/ac-square-divisibility | tag v0.1.0 → d0ed2c06 (identified, not linked from the entry); relevant files unchanged at HEAD b157f43f | auxiliary Lean modules on P(n,a,b,c) in the package (not stated in the entry) imply our Thm 1–3 at triviality level (§5b; NOVELTY.md §B′) |
| [GZ] | R.J. George (with A. Zhao), Formalizing the Andrews–Curtis conjecture (blog, June 2026), https://www.robertj1.com/ai4science/ac-conjecture-aristotle/ ; C. Zhang, A. Zhou, R.J. George, S. Gukov, A. Anandkumar, NeurIPS 2025 MATH-AI, openreview lt3Lpa4d2d | blog read in full; repo unreleased; OpenReview full text not retrieved | earlier formalization of [SMF] results (§5b) |
| [Lis] | A. Lisitsa, Stable Andrews–Curtis trivialization of AK(3) revisited, J. Comput. Algebra 16 (2025) 100041, doi:10.1016/j.jaca.2025.100041 (arXiv:2501.18601v1) | published abstract via OpenAlex; arXiv v1 | correction only: the stable AK(3) claim is withdrawn; **not used** |

### 5b. Comparison with prior formalizations
**George–Zhao [GZ].**
- *Framework.* They formalize AC moves in their own framework, not the SAIR AC.lean:
  - `Presentation (Fin N)`;
  - a rank-2 `ACMove` with 12 constructors and no inversion, and `ACEquivalent := EqvGen ACMove`;
  - `GeneralACMove`/`GeneralACEquivalent` and `StableACMove`.
- *Results.* They prove `AK_equiv_MS_w₁` (AK(n) ~ MS(n, w₁), n ≥ 2), the knot-presentation results (`theorem16_paper`,
  `proposition12_paper`) and n = 0, 1 cases (via Aristotle).
- *The mismatch.* Their section "The mismatch we fixed" reports that the rank-2 search relation lacked inversion. They
  proved `ACMove.toGeneral` / `ACEquivalent.toGeneral`.
- *Scope claimed.* They state that they "fully formalized the mathematical results in" [SMF]. The repository is announced
  but not released, so no commit can be cited and their exact theorem list cannot be checked.
- *Overlap.* The overlap is our §2a layer, in a different framework. Their blog shows no wA family, period, automorphism
  transfer, or AK(3)/AK(4) link.
- *What differs in ours.* We work directly against the official `AC.Reachable` (`ReflTransGen` of inv/mulRight/conj by
  any word), which is what the competition requires.

**Sneiderman [Sn].**
- *Framework.* Same official AC.lean (byte-identical sha256), Lean 4.29.1, standard axioms. Family
  `presentation n a b c`.
- *Results.*
  - `a_period` (period n in a) and `b_period` (period n+1 in b);
  - `residue_solvable_iff` (triviality depends only on (a mod n, b mod n+1));
  - `ParameterShift.shift_steps` (an ordinary path shifting $(a,b)$ to $(a-nt,b+(n+1)t)$);
  - `zero_a_solvable`, `zero_b_solvable`, `uniform_family` (cell (n−1,1));
  - `YInversion.solution` ((a,b,c) ⇒ (−a,−b,−c));
  - `all_parameters_two` (all of n = 2).
- *How it implies our results.* With our `MS_wA_reach_SnPres` (MS(n, wA m) ~ point (−m, m, 0)):
  - Thm 2 follows from `all_parameters_two`.
  - Thm 3 follows case by case: m ∈ nℤ ↦ a ≡ 0; m ∈ (n+1)ℤ ↦ b ≡ 0; m ≡ 1 ↦ (n−1, 1); m ≡ −1 ↦ its y-inversion.
  - Thm 1 at triviality level follows from `residue_solvable_iff` + CRT.
- *How checked.* This combination is a paper argument across two repositories. It has not been compiled as one Lean
  project.
- *What remains different.*
  - Our period is an AC-equivalence of presentations.
  - Our n = 3, 4, 5 certificates cover the cells (1,2), (2,2) at n = 3, (2,1)–(2,4) at n = 4 and (3,2), (2,3),
    (3,3), (2,4), (1,3), (4,3) at n = 5. Their stated theorems do
    not cover these cells.
  - The negative AK class in Theorem 5 reaches the cell (1,1) via `shift_steps` at $t=2$.
- *Their own novelty statement.* Their PRIOR_WORK.md disclaims novelty of substitution and automorphism techniques.

The $n=5$ comparison uses the published word rows in Table 2. The prior-art record gives the versions consulted and the limits of the older $n=3,4$ searches. [Prior-art record](NOVELTY.md)

## 6. Search record for open classes (experiments, not results)
- Search effort without success: line-wise greedy (4M nodes, maxlen 40); cyclic-canonical search (states = unordered
  pairs of cyclic words up to inversion, moves = product of any rotations of r_i and r_j^{±1}) 3M nodes for six
  representatives m ∈ {±5, ±7, ±17} and 10M nodes (maxlen 24) for reduced words yxyX, YYxyX, yxYYYX (≡5) and YxYX, yyxYX,
  YxyyyX (≡7); supermove variant (multiplication by powers 1..3 of rotations) 8M nodes; n=4: 6M nodes for yxYYX, yxyyX,
  YxYX. The same cyclic search solves the certified residues in < 6k states, so these classes are much harder for it.
  Failure of the search is not evidence that the presentations are non-trivial.
- Identity search: using a Britton-reduction word-problem solver for BS(3,4), no G-conjugacy r1(m) ~ r1(m')^{±1}
  links residues {1,2,5,7,10,11} to any other residue (conjugators up to length 7, |m'| ≤ 40). So the period and ψ-symmetry
  appear to be the only cheap reductions of this "relator-1-conjugacy" type.
- At $n=5$, the November 18 search produced six certificates for the signed representatives listed in §2d. A failed search at $m=\pm4$ coexists with published trivializations of the corresponding short representatives. The path certificates and the published table give the evidence used here.

## AI assistance

AI tools assisted with Lean formalization, path search, the literature comparison and drafting. Fable contributed to the English proof of Theorem 5 and the statement of its relationship to prior work. The Lean build and axiom audit provide the verification of the formal claims.
