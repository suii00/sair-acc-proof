# Submission candidate v1.1 — Miller–Schupp presentations MS(n, y^{-m} x y^m x^{-1}): Lean formalization against the official definitions, with prior-art accounting
SAIR Andrews–Curtis Challenge, Proof Track. Conjecture: **AC**. Direction: **proof**, as a *partial result*.
No claim is made about the full conjecture. Status: candidate, NOT submitted.

Every theorem below is kernel-checked in Lean 4 (v4.29.1, Mathlib 5e932f97) against the UNMODIFIED official
`competition/tools/lean/AC.lean` of SAIRcompetition/Andrews-Curtis @ a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e
(`AC.Reachable`, `AC.standard`; sha256 927ba318…). The build uses warningAsError and has no `sorry`/`admit`/`native_decide`.
`#print axioms` over all 59 audited theorems shows only axioms from {propext, Classical.choice, Quot.sound}: 57 use exactly
these three; `bs_pow` uses [propext] and `link_identity` uses [propext, Quot.sound]. See `logs/build_axioms_v1.1.log` and
`scripts/reproduce.sh`.

**What changed since v1 (honest scope).**
- The v1.1 prior-art check found R. Sneiderman's public Lean repository (github.com/Robby955/ac-square-divisibility,
  public since 2026-09-12, built against the same official AC.lean). It proves period and n ≤ 2 results for the
  three-parameter family (x⁻¹yⁿxy^{-(n+1)}, x⁻¹y^a x y^b x⁻¹y^c), and our MS(n, wA m) is AC-equivalent to its point
  (−m, m, 0) (our Lean `MS_wA_reach_SnPres`).
- **Consequently, the triviality content of our period theorem, MS_wA_cover and the n = 2 all-m theorem is NOT new.** It
  follows from Sneiderman's stated theorems (§2c, §5b).
- v1.1 therefore does not present these as "not found in the literature". What remains possibly new is small: Lean
  certificates for certain finite residue cells at n = 3, 4 (§2d); the AK(4) link (novelty unconfirmed); and the
  AC-equivalence (rather than triviality-iff) form of the period.
- The AK(3)/AK(4) links are presented as independent formal proofs (§2b): the AK(3) one of a known fact, the AK(4) one
  of a fact whose novelty is unconfirmed.

## 0. Conventions and terminology
x = `FreeGroup.of 0`, y = `FreeGroup.of 1`, X = x⁻¹, Y = y⁻¹.
`MS n w = ![x⁻¹yⁿx(y^{n+1})⁻¹, x w⁻¹]` = ⟨x,y | x⁻¹yⁿx = y^{n+1}, x = w⟩ (Miller–Schupp).
wA(m) = y^{-m} x y^m x⁻¹; w⋆ = y⁻¹xyx⁻¹ = wA(1); w_k = y^{-k}x⁻¹yxy; v(q) = y⁻¹xy^{1-q}x⁻¹.
AK(n) = ⟨x,y | xⁿ = y^{n+1}, xyx = yxy⟩ (Lean `AK n`).
- **AC-trivial**: `Reachable R (standard 2)`.
- **AC-equivalent presentations** (R ~ S): `Reachable R S`. This relation is symmetric (`Reachable.symm`).
- **AC-triviality transfer** (R ⇒triv S): "R AC-trivial implies S AC-trivial". This gives no AC path. `MS_wA_negate`,
  the shear/automorphism steps, and the AK links are transfers.
- **Sneiderman coordinates**: `SnPres n a b c = ![x⁻¹yⁿxy^{-(n+1)}, x⁻¹y^a x y^b x⁻¹y^c]` (our restatement, Comparison.lean).
  `MS_wA_reach_SnPres : MS n (wA m) ~ SnPres n (−m) m 0` (one inversion plus one conjugation).
  By CRT, m mod n(n+1) ↔ cell (−m mod n, m mod n+1).

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

**Theorem 4 (n = 3, 4; certified search paths).** `MS3_wA`: AC-trivial for m mod 12 ∉ {5, 7}. `MS4_wA`: AC-trivial for
m mod 20 ∉ {3, 7, 9, 11, 13, 17}.
*Prior art:*
- The cells covered by Sneiderman's general theorems are m ≡ 0,1,3,4,6,8,9,11 (mod 12) and m ≡ 0,1,4,5,8,10,12,15,16,19
  (mod 20).
- **Only our Lean-checked paths cover** m ≡ 2, 10 (mod 12) and m ≡ 2, 6, 14, 18 (mod 20). I did not find these in the
  sources checked.
- These are finite base cases (each one presentation plus periodicity). Benchmark tables may contain them.

**Theorem 5 (AK links; independent formal proofs).**
- `MS3_wA5_iff_AK3`: MS(3, wA 5) AC-trivial ⇔ AK(3) AC-trivial. Hence `MS3_wA_of_AK3`: if AK(3) is AC-trivial then
  MS(3, wA m) is AC-trivial for every m.
  This is **a known fact, in a stronger form**:
  - MS(3, wA 5) ~ ⟨x⁻¹y³x = y⁴, x = y⁻¹x²y⁻¹⟩, which Shehper et al. v2 §3 state is AC-equivalent to AK(3).
  - Carreras 2026 Thm 4 certifies that equivalence with an explicit 22-move path.
  - Fagan et al. App. F put it in class 13₁.
- `MS4_wAm9_iff_AK4`, `MS4_wA_9_11_of_AK4`: MS(4, wA(−9)) AC-trivial ⇔ AK(4) AC-trivial; if AK(4) is AC-trivial, then
  m ≡ 9, 11 (mod 20) are covered. **Novelty unconfirmed**: Fagan et al. class 15₁ contains MS(4, yxyx⁻¹), but I did not
  find a statement that 15₁ is AK(4)'s class.
- Method (automorphism x ↦ xy^k plus one BS(n,n+1) identity) is standard: Panteleev–Ushakov Lemma 3.1, Prop 3.7.
- In Sneiderman coordinates both MS(3, wA 5) and MS(4, wA(−9)) are the cell (1, 1).

## 2. Classification of results and theorem ↔ Lean correspondence
Files are under `lean/ACProof/`. See §5 for the sources.

### 2a. Formalization of known results (credit to the original authors)
An earlier, independent formalization of these results (and, by the authors' account, of all results of [SMF]) exists:
George–Zhao, in their own framework and not against the official AC.lean, repository unreleased (§5b).
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

### 2b. Independent formal proofs of known (or claimed) AK links
| Statement | Lean name | File | Status |
|---|---|---|---|
| automorphism φ_k: x ↦ xy^k, y ↦ y, with inverse φ_{−k} | `phiK`, `phiK_inv_comp`, `phiK_comp_MS`, `phiK_std`, `std_of_xyk` (def/helper lemmas, not separately listed in Check.lean; used by the audited theorems) | AK3Link | standard (PU Lemma 3.1) |
| key BS(3,4) identity; φ₃(MS(3,wA 5)) ~ MS(3, w_8) | `link_identity`, `phi_MS3_wA5_reach_wk8` | AK3Link | proof ingredient |
| MS(3, wA 5) triv ⇔ AK(3) triv; AK(3) triv ⇒ all MS(3, wA m) triv | `MS3_wA5_iff_AK3`, `MS3_wA_of_AK3` | AK3Link | KNOWN ([SMF] v2 §3; [Car] Thm 4; [Fag] App. F) |
| BS(4,5) identities; φ₋₆(MS(4,wA(−9))) ~ MS(4, w_{−9}) | `bs_pow`, `link4_identity`, `phi_MS4_wAm9_reach_wkm9` | AK4Link | proof ingredient |
| MS(4, wA(−9)) triv ⇔ AK(4) triv; AK(4) triv ⇒ m ≡ 9, 11 (mod 20) | `MS4_wAm9_iff_AK4`, `MS4_wA_9_11_of_AK4` | AK4Link | novelty unconfirmed |

### 2c. Results whose triviality content is implied by prior work (Sneiderman 2026); our proofs are independent
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

### 2d. Finite cells not found in the sources checked (novelty NOT confirmed)
| Statement | Lean name | File |
|---|---|---|
| Thm 4, n = 3 (new cells m ≡ 2, 10 mod 12) | `MS3_wA` (bases `MS3_wA_m10`, `MS3_wA_m2`, `MS3_wA_m1`) | N3 |
| Thm 4, n = 4 (new cells m ≡ 2, 6, 14, 18 mod 20) | `MS4_wA` (bases `MS4_wA_m2`, `_m6`, `_m14` [m=−6], `_m18` [m=−2], `_m19` [m=−1]) | N4 |

### 2e. Unproven (open; no claim)
- MS(3, wA m) for m ≡ ±5 mod 12 is unproven. It is equivalent in triviality to AK(3).
- MS(4, wA m) for m ≡ ±3, ±7 mod 20 is unproven. So is m ≡ ±9 mod 20, which is equivalent to AK(4).
- MS(n, wA m) for n ≥ 5 outside Theorem 3, and AK(n) for n ≥ 3, are unproven.
- No stable-AC statement is made or used. Lisitsa's 2025 stable AK(3) claim was withdrawn in the published version (§5).
- The AC conjecture itself is not addressed.
- Search failures (§6) are NOT evidence of non-triviality.

## 3. Paper proofs (human-checkable without Lean)
Let G = F(x,y)/⟨⟨r0⟩⟩, r0 = x⁻¹yⁿxy^{-(n+1)}, K: x⁻¹yⁿx = y^{n+1}; r1(m) = x·wA(m)⁻¹ = x·x y^{-m} x⁻¹ y^m.
AC fact (Lean `reach_slot1_mod`, `reach_slot1_conj`): if the image of r1' in G is conjugate to the image of r1, then
(r0, r1) ~ (r0, r1').

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
xy^{q-1}x⁻¹), bases q = 0 (w⋆), q = 1 (y⁻¹) and the explicit 19-move path for q = −1:
 • m = 5 ≡ -1: write -1 = (-1)·2 + 1, reduction mod 2 gives the second relator for v(-1) = y⁻¹ x y² x⁻¹. Explicit path
   (r0, r1) = (Xyy x YYY, xxYYXy) [X = x⁻¹, Y = y⁻¹]; "c_i g" = conjugate relator i by g (g r g⁻¹);
   "i/j" = r_i·r_j⁻¹; "i·j" = r_i·r_j; "inv i"; words reduced cyclically-free only where the move does so:
    0 c0 x → (yyxYYYX, xxYYXy)    1 c0 Y → (yxYYYXy, ·)   2 0/1 → (yxYXX, ·)   3 c0 Y → (xYXXy, ·)   4 c0 X → (YXXyx, ·)
    5 c1 X → (·, xYYXyx)   6 1/0 → (·, xYYxy)   7 c0 y → (XXyxY, ·)   8 c1 X → (·, YYxyx)   9 c1 y → (·, YxyxY)
   10 1/0 → (·, Yxxx)   11 c1 x → (·, xYxx)   12 1·0 → (·, xxY)   13 0/1 → (XXyX, ·)   14 c0 x → (XyXX, ·)
   15 0·1 → (X, ·)   16 inv 1 → (·, yXX)   17 1/0 → (·, yX)   18 1/0 → (X, y), then inv 0 → (x, y).
   Each line can be checked by free reduction by hand (e.g. step 2: yxYYYXy·(xxYYXy)⁻¹ = yxYYYXy·YxyyXX = yxYXX).

The n = 3, 4 bases (52/21/45 and 25/49/50/26/132 moves) were found by greedy search (`search/greedy.py`).
`search/emitn2.py` turns each move into one official `Step`, and Lean checks each one (`Tactics.lean`).

## 5. Sources (verified; version, theorem numbers, use)
| Key | Work | Version checked | Used for |
|---|---|---|---|
| [AC] | J.J. Andrews, M.L. Curtis, Free groups and handlebodies, Proc. AMS 16 (1965) 192–195 | journal | statement of the conjecture |
| [OFF] | SAIRcompetition/Andrews-Curtis, `competition/tools/lean/AC.lean` | commit a0fd6e6f, sha256 927ba318… | official definitions (unchanged) |
| [MiS] | C.F. Miller III, P.E. Schupp, Some presentations of the trivial group, Contemp. Math. 250 (1999) 113–115 | MR1732210 | definition of MS(n, w) |
| [AK] | S. Akbulut, R. Kirby, Topology 24 (1985) 375–390 | journal | definition of AK(n) |
| [MMS] | A.D. Myasnikov, A.G. Myasnikov, V. Shpilrain, On the Andrews–Curtis equivalence, Contemp. Math. 296 (2002) 183–198 | arXiv:math/0302080v1 | Prop 1.1 (AK(2)), Prop 1.3 (AK(n) ~ MS(n, w_1)) |
| [SMF] | A. Shehper, A. Medina-Mardones, et al., S. Gukov, What makes math problems hard for reinforcement learning: a case study | arXiv:2408.15332v2 (11 Feb 2025) | Thm 2, 3, Prop 5, Thm 6, 7, Cor 9; §3 (length-14 MS(3,·) ~ AK(3)) |
| [Car] | J. Carreras, Machine-checkable equivalence certificates at the length-14 Andrews–Curtis frontier | arXiv:2607.23611v1; repo joe-carr-data/ac-certificates @ d347fc47 (Python verifier, no Lean) | Thm 4: MS(3, y⁻¹x²y⁻¹) ~ AK(3) |
| [Fag] | L. Fagan, M. Tarquini, A. Shehper, et al., S. Gukov, The Two-Hump Problem | arXiv:2606.21611v1; repo Math-AI-Caltech/ACSolverX @ 6a12515f (JAX, no Lean) | App. F classes 13₁ (AK(3)), 15₁ |
| [PU] | P. Panteleev, A. Ushakov, Conjugacy search problem and the Andrews–Curtis conjecture | arXiv:1609.00325 | Lemma 3.1 (automorphisms preserve AC-triviality), Thm 2.3, Prop 3.7 / Cor 3.8 (standard techniques) |
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
  - Our n = 3, 4 certificates cover the cells (1,2), (2,2) at n = 3 and (2,1)–(2,4) at n = 4. Their stated theorems do
    not cover these cells.
  - Our AK(3)/AK(4) links concern the cell (1,1).
- *Their own novelty statement.* Their PRIOR_WORK.md disclaims novelty of substitution and automorphism techniques.

**Not checked:** exhaustive Google Scholar; Myasnikov 1999 and Havas–Ramsay data files; the Fagan/Carreras datasets
(which may contain our n = 3, 4 cells); the OpenReview full text of [GZ]; Sneiderman's paper beyond keyword search and
his research supplements. Full record: NOVELTY.md and research/lit/ (map.md, log.md, extracts.json, report.html).

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


