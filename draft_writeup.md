# Submission candidate v1 — AC-triviality of Miller–Schupp presentations MS(n, y^{-m} x y^m x^{-1})
SAIR Andrews–Curtis Challenge, Proof Track. Conjecture: **AC**. Direction: **proof**, as a *partial result*.
No claim is made about the full conjecture. Status: candidate, NOT submitted.

Every theorem below is kernel-checked in Lean 4 (v4.29.1, Mathlib 5e932f97) against the UNMODIFIED official
`competition/tools/lean/AC.lean` of SAIRcompetition/Andrews-Curtis @ a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e
(`AC.Reachable`, `AC.standard`). Build with warningAsError; no `sorry`/`admit`/`native_decide`; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for all 48 audited theorems (`logs/build_axioms_v1.log`, `scripts/reproduce.sh`).

## 0. Conventions and terminology
x = `FreeGroup.of 0`, y = `FreeGroup.of 1`, X = x⁻¹, Y = y⁻¹.
`MS n w = ![x⁻¹yⁿx(y^{n+1})⁻¹, x w⁻¹]` = ⟨x,y | x⁻¹yⁿx = y^{n+1}, x = w⟩ (Miller–Schupp).
wA(m) = y^{-m} x y^m x⁻¹; w⋆ = y⁻¹xyx⁻¹ = wA(1); w_k = y^{-k}x⁻¹yxy; v(q) = y⁻¹xy^{1-q}x⁻¹.
- **AC-trivial**: `Reachable R (standard 2)`.
- **AC-equivalent presentations** (R ~ S): `Reachable R S`. This is symmetric (`Reachable.symm`), so a one-directional
  Lean statement `Reachable R S` already gives AC-equivalence.
- **AC-triviality transfer** (R ⇒triv S): "R AC-trivial implies S AC-trivial". This is weaker than R ~ S: it gives no
  AC path between R and S. `MS_wA_negate` is only a transfer.

## 1. Main results
**Theorem 1 (period; all n).** `MS_wA_period`, `MS_wA_period_mul`: for all n ∈ ℕ and m, t ∈ ℤ,
MS(n, wA m) ~ MS(n, wA(m + t·n(n+1))). Corollary `MS_wA_of_residues` (n > 0): if MS(n, wA r) is AC-trivial for every
0 ≤ r < n(n+1), then MS(n, wA m) is AC-trivial for every m.

**Theorem 2 (n = 2, all integers).** For every m ∈ ℤ, MS(2, y^{-m} x y^m x⁻¹) is AC-trivial.
- Proof A (`MS2_wA_all'`, file MS2Alt.lean; no search path): ℤ = 2ℤ ∪ 3ℤ ∪ (1+6ℤ) ∪ (−1+6ℤ), and each set is covered by a
  general family (`MS_wA_cover`): multiples of n (`MS_wA_mult`), multiples of n+1 (`MS_wA_mult_succ`), ±1 mod n(n+1)
  (`MS_wA_pm_one` = period + `MS_wA_one` + `MS_wA_negate`).
- Proof B (`MS2_wA_all`, file MS2All.lean; kept as an alternative): shift by 3 on v(q) plus a certified 19-move path.

**Theorem 3 (general families; all n).** `MS_wA_cover`: MS(n, wA m) is AC-trivial whenever
m ∈ nℤ ∪ (n+1)ℤ ∪ (1 + n(n+1)ℤ) ∪ (−1 + n(n+1)ℤ).

**Theorem 4 (instances n = 3, 4; certified search paths).** `MS3_wA`: AC-trivial for m mod 12 ∉ {5, 7}.
`MS4_wA`: AC-trivial for m mod 20 ∉ {3, 7, 9, 11, 13, 17}.

## 2. Classification of results and theorem ↔ Lean correspondence
Files are under `lean/ACProof/`. "Src" gives the precise source (see §5).

### 2a. Formalization of known results (credit to the original authors)
| Statement | Lean name | File | Src |
|---|---|---|---|
| AC-moves preserve the normal closure; triviality invariance | `Reachable.ncl_eq`, `Reachable.presentsTrivialGroup_iff`, `Reachable.presentsTrivialGroup` | Basic | standard |
| R ~ S is symmetric; left mult., swap, permutations, endomorphism transport | `Reachable.symm`, `reach_mulLeft`, `reach_swap`, `reach_perm`, `Reachable.map`, `Reachable.relabel` | Basic | standard |
| multiply a relator by any element of the normal closure of another | `reach_mul_normalClosure` | Consequence | standard |
| MS(1, w) AC-trivial ∀w (x-exponent sum 0) | `MS1_reachable` | MS1 | [SMF] Thm 2 |
| MS(n, w⋆) AC-trivial ∀n | `MS_wstar_reachable` | MS1 | [SMF] Thm 3 |
| MS(n, w_k) ~ MS(n, w_{k+1}) and ~ for all k, k' | `MS_wk_succ`, `MS_wk_equiv` | MSwk | [SMF] Thm 6 |
| MS(2, w_k) AC-trivial ∀k | `MS2_wk_reachable` | MS2 | [SMF] Cor 9 (our proof uses our own certified 21-move path for w_3 instead of AK(2)) |
| AK(n) ~ MS(n, w_1) | `AK_reach_MS` | AK | [MMS] Prop 1.3; [SMF] Prop 5 |
| AK(2) AC-trivial | `AK2_reachable` | AK | [MMS] Prop 1.1 |
| MS(n, w_k) ~ P(n, k) | `MS_reach_P` | AK | [SMF] Thm 7 |

### 2b. Corollaries of known lemmas (short arguments; possibly folklore)
| Statement | Lean name | File |
|---|---|---|
| MS(n, y^k) AC-trivial | `MS_ypow_reachable` | MillerSchupp |
| m ∈ nℤ | `MS_wA_mult` (key identity `conj_mult`) | NewFamilies |
| m = ±n, ±(n+1); reduction MS(n, wA(qn+j)) ~ MS(n, y^{-j}xy^{j-q}x⁻¹) | `MS_wA_neg`, `MS_wA_self`, `MS_wA_succ`, `MS_wA_negsucc`, `MS_wA_reduce`, `MS_wA_diag` | NewFamilies |
| m ∈ (n+1)ℤ | `MS_wA_mult_succ` | General |
| m = 1 | `MS_wA_one` (= w⋆, [SMF] Thm 3) | General |

### 2c. Results under novelty investigation (not found in the sources of §5; novelty NOT confirmed)
| Statement | Lean name | File |
|---|---|---|
| Thm 1, period n(n+1) | `MS_wA_period`, `MS_wA_period_mul`, `MS_wA_of_residues` | Period |
| transfer: MS(n, wA(−m)) AC-trivial ⇒ MS(n, wA m) AC-trivial | `MS_wA_negate` | General |
| m ≡ ±1 mod n(n+1) | `MS_wA_neg_one`, `MS_wA_pm_one` | General |
| Thm 3 | `MS_wA_cover` | General |
| Thm 2, proof A | `MS2_wA_all'` | MS2Alt |
| Thm 2, proof B; shift on v(q) | `MS2_wA_all`, `MS2_v_shift`, `MS2_v_reachable` | MS2All |
| Thm 4, n = 3 | `MS3_wA` (bases `MS3_wA_m10`, `MS3_wA_m2`, `MS3_wA_m1`) | N3 |
| Thm 4, n = 4 | `MS4_wA` (bases `MS4_wA_m2`, `_m6`, `_m14` [m=−6], `_m18` [m=−2], `_m19` [m=−1]) | N4 |

### 2d. Unproven (open; no claim)
MS(3, wA m) for m ≡ ±5 mod 12; MS(4, wA m) for m ≡ ±3, ±7, ±9 mod 20; MS(n, wA m) for n ≥ 5 outside Theorem 3; AK(n) for
n ≥ 3; any stable-AC statement; the AC conjecture. Search failures (§6) are NOT evidence of non-triviality.

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

## 5. Sources used (verified; version, theorem numbers, use)
| Key | Work | Version checked | Used for |
|---|---|---|---|
| [AC] | J.J. Andrews, M.L. Curtis, Free groups and handlebodies, Proc. AMS 16 (1965) 192–195 | journal | statement of the conjecture |
| [OFF] | SAIRcompetition/Andrews-Curtis, `competition/tools/lean/AC.lean` | commit a0fd6e6f, sha256 927ba318… | official definitions (unchanged) |
| [MiS] | C.F. Miller III, P.E. Schupp, Some presentations of the trivial group, Contemp. Math. 250 (1999) 113–115 | MR1732210 | definition of MS(n, w) |
| [AK] | S. Akbulut, R. Kirby, Topology 24 (1985) 375–390 | journal | definition of AK(n) |
| [MMS] | A.D. Myasnikov, A.G. Myasnikov, V. Shpilrain, On the Andrews–Curtis equivalence, Contemp. Math. 296 (2002) 183–198 | arXiv:math/0302080v1 | Prop 1.1 (AK(2) AC-trivial), Prop 1.3 (AK(n) ~ MS(n, w_1)) |
| [SMF] | A. Shehper, A. Medina-Mardones, et al., S. Gukov, What makes math problems hard for reinforcement learning: a case study | arXiv:2408.15332v2 (11 Feb 2025) | Thm 2 (MS(1,w)), Thm 3 (MS(n,w⋆)), Prop 5 (= [MMS] Prop 1.3), Thm 6 (w_k equivalence), Thm 7 (P(n,k)), Cor 9 (MS(2,w_k)) |

Consulted only for the novelty check (not used in proofs): D. Panteleev, A. Ushakov, arXiv:1609.00325; G. Havas, C. Ramsay,
IJAC 13 (2003) 61–68; A. Lisitsa, Ex. Countex. 6 (2024) 100168; M.R. Bridson, arXiv:1504.04187. Not checked:
exhaustive Google Scholar, Myasnikov 1999 data, Havas–Ramsay data, 2025–26 follow-ups.

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


