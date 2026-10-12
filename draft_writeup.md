# DRAFT — Formalized AC-triviality results for Miller–Schupp and Akbulut–Kirby families (SAIR ACC Proof Track)
Conjecture: **AC**. Direction: **proof**, as a *partial result* (no claim about the full conjecture).
Status: DRAFT, not submitted. All statements below are kernel-checked in Lean 4 (v4.29.1, Mathlib 5e932f97) against the
UNMODIFIED official `competition/tools/lean/AC.lean` (`AC.Reachable`, `AC.standard`, `AC.PresentsTrivialGroup`).
Build: `lake build AC ACProof` (warningAsError). No `sorry`/`admit`/`native_decide`; `#print axioms` for every theorem
= `[propext, Classical.choice, Quot.sound]`. The only change to the repo is the line `[[lean_lib]] ACProof` in lakefile.toml.

## Conventions
x = `FreeGroup.of 0`, y = `FreeGroup.of 1`. `MS n w = ![x⁻¹ yⁿ x y^{-(n+1)}, x w⁻¹]`, i.e. MS(n,w) = ⟨x,y | x⁻¹yⁿx = y^{n+1}, x = w⟩
[Miller–Schupp 1999]. `AK n = ![xⁿ y^{-(n+1)}, xyx(yxy)⁻¹]` [Akbulut–Kirby 1985]. w_k = y^{-k}x⁻¹yxy, w⋆ = y⁻¹xyx⁻¹,
wA(m) = y^{-m}x y^m x⁻¹, v(q) = y⁻¹ x y^{1-q} x⁻¹. All results hold for every n : ℕ (incl. n = 0, beyond the usual n ≥ 1).

## A. General infrastructure (any rank n) — standard facts, formalized here
- `reach_mul_normalClosure`: relator i may be multiplied by any element of the normal closure of relator j (i ≠ j).
- `Reachable.presentsTrivialGroup_iff`, `Reachable.ncl_eq`: AC-moves preserve the normal closure / triviality.
- `Reachable.symm`; `reach_mulLeft(_inv)`, `reach_mulRight_inv`; `reach_swap`, `reach_perm` (all relator permutations);
  `Reachable.map`, `Reachable.relabel` (transport along free-group endomorphisms / generator permutations).

## B. Known results, newly formalized (credit to original authors)
| Lean | Statement | Source |
|---|---|---|
| `MS_ypow_reachable` | MS(n, yᵏ) AC-trivial ∀n,k | elementary |
| `MS1_reachable` | MS(1,w) AC-trivial ∀w with x-exponent sum 0 | Shehper et al., arXiv:2408.15332v2, Thm 2 (Thm B(i)) |
| `MS_wstar_reachable` | MS(n,w⋆) AC-trivial ∀n | ibid. Thm 3 (B(ii)); Lisitsa 2024 for n=3..8, 2025 for n=9 |
| `MS_wk_equiv` | MS(n,w_k) ~ MS(n,w_k') ∀n,k,k' | ibid. Thm 6 |
| `MS2_wk_reachable` | MS(2,w_k) AC-trivial ∀k | ibid. Cor 9 (B(iii)); our proof uses our own 21-move certified path for MS(2,w_3) instead of AK(2)+MMS |
| `AK_reach_MS` | AK(n) ~ MS(n,w_1) ∀n | Myasnikov–Myasnikov–Shpilrain, Contemp. Math. 296 (2002), Prop 1.3 |
| `AK2_reachable` | AK(2) AC-trivial | MMS02 Prop 1.1(a) (Myasnikov), Gersten (stably); here a corollary of the above |
| `MS_reach_P` | MS(n,w_k) ~ P(n,k) ∀n,k | Shehper et al. v2 Thm 7 |

## C. Results we did not find in the literature (novelty plausible, NOT confirmed)
1. `MS_wA_mult`: ∀n ∈ ℕ, q ∈ ℤ, MS(n, y^{-qn} x y^{qn} x⁻¹) is AC-trivial.
   Key lemma `conj_mult`: in BS(n,n+1)=F/⟨⟨x⁻¹yⁿxy^{-(n+1)}⟩⟩, y^{-qn} x y^{qn} = x y^{-q}.
2. `MS_wA_succ`, `MS_wA_negsucc`: MS(n, wA(±(n+1))) AC-trivial ∀n.
3. `MS_wA_reduce`: ∀n,q,j: MS(n, wA(qn+j)) ~ MS(n, y^{-j} x y^{j-q} x⁻¹) (reduction mod n).
4. `MS2_v_shift`: MS(2, v(q)) ~ MS(2, v(q+3)) — the relator for q+3 is the y⁴-conjugate of that for q modulo the
   first relator (identity in BS(2,3): uses x y³ x⁻¹ = y², y⁴x = xy⁶, y⁶ = xy⁹x⁻¹ central w.r.t. xy^{q-1}x⁻¹).
   Discovered by tracking conjugators along a greedy-search path from q=5 to q=2.
5. `MS2_v_reachable`: ∀q ∈ ℤ, MS(2, y⁻¹ x y^{1-q} x⁻¹) AC-trivial (bases q=0: w⋆; q=1: y⁻¹; q=-1: certified 19-move path).
6. **`MS2_wA_all`: ∀m ∈ ℤ, MS(2, y^{-m} x y^m x⁻¹) is AC-trivial.**
7. `MS_wA_period` / `MS_wA_period_mul` / `MS_wA_of_residues` (round 6): ∀n, m, t: MS(n, wA m) ~ MS(n, wA(m + t·n(n+1))).
   So for each n, AC-triviality of MS(n, wA m) for all m reduces to the n(n+1) residues 0 ≤ m < n(n+1) (needs n > 0).
8. `MS_wA_mult_succ` (round 6): ∀n, q: MS(n, wA(q(n+1))) AC-trivial (reduce with j=q gives y^{-q}, then MS_ypow).
9. **`MS3_wA` (round 6): ∀m ∈ ℤ with m mod 12 ∉ {5, 7}, MS(3, y^{-m} x y^m x⁻¹) is AC-trivial.**
   Residues 0,3,6,9 (mult of 3), 4,8 (mult of 4), 1 (w⋆); residues 2, 10, 11 via certified search paths for
   m = -10, -2, -1 (52, 21, 45 AC moves; each move an official `Step`, checked by Lean).
   OPEN for n=3: residues 5 and 7 (greedy search up to 4M nodes failed; this is NOT evidence of non-triviality).

10. **`MS4_wA` (round 7): ∀m ∈ ℤ with m mod 20 ∉ {3,7,9,11,13,17}, MS(4, wA m) is AC-trivial.** Residues 2, 6, 14,
   18, 19 use certified search paths for m = 2, 6, -6, -2, -1 (25/49/50/26/132 moves; Lean names MS4_wA_m2, _m6,
   _m14 (= m −6), _m18 (= m −2), _m19 (= m −1)).
11. **`MS_wA_negate` (round 7): MS(n, wA(−m)) AC-trivial ⇒ MS(n, wA m) AC-trivial.** Proof: ψ: x↦x, y↦y⁻¹ maps
   r0 = x⁻¹yⁿxy^{-(n+1)} to x⁻¹y^{-n}xy^{n+1} = (y^{-(n+1)} r0 y^{n+1})⁻¹ and wA(−m) to wA(m); AC-reachability is preserved
   by endomorphisms (Lean `Reachable.map`) and ψ(x, y) = (x, y⁻¹) is trivial.
   Corollary `MS_wA_neg_one`/`MS_wA_pm_one`: ∀n, MS(n, y x y⁻¹ x⁻¹) and all m ≡ ±1 mod n(n+1) are AC-trivial.
   (MS(n,[y,x])-type words may well be known/folklore; not found in the sources checked.)

### C'. Remaining open residue classes (after period n(n+1) and the symmetry m ↔ −m)
- n = 3: the single class {5, 7} mod 12 (5 ≡ −7). Open.
- n = 4: three classes {3,17}, {7,13}, {9,11} mod 20. Open.
- Search effort without success: line-wise greedy (4M nodes, maxlen 40); cyclic-canonical search (states = unordered
  pairs of cyclic words up to inversion, moves = product of any rotations of r_i and r_j^{±1}) 3M nodes for six
  representatives m ∈ {±5, ±7, ±17} and 10M nodes (maxlen 24) for reduced words yxyX, YYxyX, yxYYYX (≡5) and YxYX, yyxYX,
  YxyyyX (≡7); supermove variant (multiplication by powers 1..3 of rotations) 8M nodes; n=4: 6M nodes for yxYYX, yxyyX,
  YxYX. The same cyclic search solves the certified residues in < 6k states, so these classes are much harder for it.
  Failure of the search is not evidence that the presentations are non-trivial.
- Identity search: using a Britton-reduction word-problem solver for BS(3,4), no G-conjugacy r1(m) ~ r1(m')^{±1}
  links residues {1,2,5,7,10,11} to any other residue (conjugators up to length 7, |m'| ≤ 40). So the period and ψ-symmetry
  appear to be the only cheap reductions of this "relator-1-conjugacy" type.

### C''. Paper re-derivation of the n = 2 all-m theorem (independent of Lean; human-checkable)
Notation: X=x, Y=y in G = F(x,y)/⟨⟨r0⟩⟩, r0 = x⁻¹yⁿx y^{-(n+1)}, so K: x⁻¹yⁿx = y^{n+1}. r1(m) = x·wA(m)⁻¹ = x·x y^{-m} x⁻¹ y^m.
AC fact used throughout (standard; Lean `reach_slot1_mod` + `reach_slot1_conj`): if in G the image of r1' equals a conjugate
of the image of r1, then (r0, r1) ~AC (r0, r1').

Step 1 (period). From K: x y^{n+1} x⁻¹ = yⁿ, hence (i) x y^{(n+1)k} x⁻¹ = y^{nk} and (ii) y^{nk} x = x y^{(n+1)k}.
Put N = n(n+1), D_m = x y^{-m} x⁻¹, so r1(m) = x D_m y^m.
 • r1(m+N) = x·D_m·(x y^{-N} x⁻¹)·y^{m+N} = x D_m y^{-n²} y^{m+N} = x D_m y^{m+n}    [by (i), k = -n].
 • y^{n²} r1(m) y^{-n²} = (y^{n²} x) D_m y^{m-n²} = x y^{N} D_m y^{m-n²}             [by (ii), k = n].
   y^N = x y^{(n+1)²} x⁻¹ by (i) (k = n+1); both y^N and D_m are x·(power of y)·x⁻¹, so they commute:
   = x D_m y^{N} y^{m-n²} = x D_m y^{m+n}.
 So r1(m+N) is conjugate to r1(m) in G, and MS(n,wA m) ~ MS(n, wA(m+N)). For n=2, N=6.

Step 2 (residues mod 6, n = 2).
 • m ∈ {0,2,4}: m = 2q. From (ii) one gets y^{-nq} x y^{nq} = x y^{-q} in G, so wA(2q) = x y^{-q} x⁻¹ and
   r1 = x·x y^{q} x⁻¹, conjugate (by x⁻¹) to x y^{q}. Thus MS(2,wA(2q)) ~ (r0, x y^{q}). Using the second relator,
   AC moves replace every x in r0 by y^{-q} (Lean `subst_reachable`), turning r0 into y^{q}y²y^{-q}y^{-3} = y⁻¹;
   then (y⁻¹, x y^q) → (y⁻¹, x) → (x, y). (Lean: `MS_wA_mult`, `MS_ypow_reachable`.)
 • m = 3 = n+1: wA(3) reduces (j = q = 1 in reduction mod n) to y^{-1}; same argument.
 • m = 1: wA(1) = y⁻¹xyx⁻¹ = w⋆; MS(n,w⋆) is AC-trivial (Shehper et al.; Lean `MS_wstar_reachable`).
 • m = 5 ≡ -1: write -1 = (-1)·2 + 1, reduction mod 2 gives the second relator for v(-1) = y⁻¹ x y² x⁻¹. Explicit path
   (r0, r1) = (Xyy x YYY, xxYYXy) [X = x⁻¹, Y = y⁻¹]; "c_i g" = conjugate relator i by g (g r g⁻¹);
   "i/j" = r_i·r_j⁻¹; "i·j" = r_i·r_j; "inv i"; words reduced cyclically-free only where the move does so:
    0 c0 x → (yyxYYYX, xxYYXy)    1 c0 Y → (yxYYYXy, ·)   2 0/1 → (yxYXX, ·)   3 c0 Y → (xYXXy, ·)   4 c0 X → (YXXyx, ·)
    5 c1 X → (·, xYYXyx)   6 1/0 → (·, xYYxy)   7 c0 y → (XXyxY, ·)   8 c1 X → (·, YYxyx)   9 c1 y → (·, YxyxY)
   10 1/0 → (·, Yxxx)   11 c1 x → (·, xYxx)   12 1·0 → (·, xxY)   13 0/1 → (XXyX, ·)   14 c0 x → (XyXX, ·)
   15 0·1 → (X, ·)   16 inv 1 → (·, yXX)   17 1/0 → (·, yX)   18 1/0 → (X, y), then inv 0 → (x, y).
   Each line can be checked by free reduction by hand (e.g. step 2: yxYYYXy·(xxYYXy)⁻¹ = yxYYYXy·YxyyXX = yxYXX).
 Hence MS(2, wA m) is AC-trivial for every m. (This is a different decomposition from the Lean proof, which uses the
 shift by 3 on v(q); both routes rely on the same 19-move base path.)

Novelty check performed: Shehper et al. v2 (families: MS(1,w), MS(n,w⋆), MS(2,w_k); dataset n≤7, |w|≤7 includes wA(m) for
|m|≤2 numerically); MMS02; Panteleev–Ushakov arXiv:1609.00325 (only random n=2 instances, Tables 2–4); Lisitsa 2024/2025
(only w⋆); web search for Miller–Schupp AC-trivial families. Not checked: exhaustive Google Scholar, Myasnikov 1999 tables,
Havas–Ramsay data, Burns–Macedońska full text, 2025–26 ML follow-ups. Results 1–3 are one-substitution arguments
(possibly folklore); results 4–6 are slightly less immediate.

## D. What is NOT established
AK(n), n ≥ 3; MS(3, wA m) for m ≡ ±5 (mod 12); MS(4, wA m) for m ≡ ±3, ±7, ±9 (mod 20); MS(n, wA m), n ≥ 5, outside
nℤ ∪ (n+1)ℤ ∪ (±1 + n(n+1)ℤ); any stable-AC result; the AC conjecture itself.

## E. Reproducibility
Search-then-certify: `search/greedy.py` (greedy AC search on rank-2 tuples), `emit.py`/`emitq.py` emit one official
`Step` per move; each is checked by Lean (`step_tac`: rfl/simp/group on free-group words).

## References
Andrews–Curtis, Proc. AMS 16 (1965) 192–195. Akbulut–Kirby, Topology 24 (1985) 375–390. Miller–Schupp, Contemp. Math. 250 (1999)
113–115. Myasnikov–Myasnikov–Shpilrain, Contemp. Math. 296 (2002) 183–198, arXiv:math/0302080. Shehper, Medina-Mardones, Fagan,
Lewandowski, Gruen, Qiu, Kucharski, Wang, Gukov, arXiv:2408.15332 (v2). Lisitsa, Ex. Countex. 6 (2024) 100168; Ex. Countex. 8 (2025)
(SSRN 5100345). Panteleev–Ushakov, arXiv:1609.00325. Havas–Ramsay, IJAC 13 (2003) 61–68. Bridson, arXiv:1504.04187.
Burns–Macedońska, Bull. LMS 25 (1993) 513–526. Official statement: SAIRcompetition/Andrews-Curtis @ a0fd6e6f, AC.lean.
