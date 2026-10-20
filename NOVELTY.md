# Novelty record

## v1.1 update (2026-10-20 JST) — George/Zhao, Sneiderman, Lisitsa correction, Carreras/Fagan repos
Method and sources: research/lit/ (map.md, log.md, extracts.json, report.html; the source copies in research/lit/sources/
are not committed).

### A. Robert Joseph George (with Aaron Zhao), "Formalizing the Andrews–Curtis conjecture" (blog, June 2026)
URL: https://www.robertj1.com/ai4science/ac-conjecture-aristotle/ (sections "A closer audit with Aristotle" and "The
mismatch we fixed"). Related: Zhang, Zhou, George, Gukov, Anandkumar, NeurIPS 2025 MATH-AI,
https://openreview.net/forum?id=lt3Lpa4d2d (full text not retrieved: bot check).
**Repository: not public.** The page says "We plan to release the full repository soon". I found no GitHub link, and
`gh search` found no repo, so **no commit can be cited**.
- **Their definitions** (own, NOT the SAIR AC.lean):
  - `Presentation (Fin N)` with relator lists.
  - Rank-2 `ACMove`: 12 constructors (4 multiplications, 8 conjugations by x^{±1}, y^{±1}; no inversion).
  - `ACEquivalent := Relation.EqvGen ACMove`.
  - `GeneralACMove N` (multiply r_i r_j^{±1}, invert, conjugate by a generator^{±1}) and `GeneralACEquivalent`.
  - `StableACMove` on Σ N, Presentation (Fin N).
  - The conjectures (`stable_AC_conjecture` etc.) are stated as open Props.
- **Their theorems shown:**
  - `AK n`, `balanced_AK`; `AK_equiv_MS_w₁ (n) (2 ≤ n) : GeneralACEquivalent 2 (AK n) (MS n w₁ …)`.
  - The knot results `theorem16_paper` and `proposition12_paper`.
  - The Aristotle-generated `andrewsCurtis_n0`/`_n1`, plus normal-closure invariance.
  - `ACMove.toGeneral` and `ACEquivalent.toGeneral` (the "mismatch fixed": the rank-2 search relation lacked inversion).
  - They claim to have "fully formalized the mathematical results in" Shehper et al. 2408.15332. That would include
    MS(1,w), MS(n,w⋆), MS(n,w_k), AK(n) ~ MS(n,w_1), Thm 7 and the knot results.
- **Overlap with us:**
  - Our §2a "known results" layer: AK def, `AK_reach_MS`, MS1/w⋆/w_k families, invariance lemmas.
  - Theirs is an independent earlier formalization of the same known mathematics, in a different framework, and not
    checked against the official AC.lean.
  - Their blog shows no wA family, no period, no automorphism transfer (Reachable.map), and no AK(3)/AK(4) link.
  - The full contents cannot be checked until the repository is released.
- **Consequence:**
  - No "first formalization" claim for any Shehper et al. result.
  - Our §2a is "re-formalization against the official definitions".

### B. Robert Sneiderman, github.com/Robby955/ac-square-divisibility (public since 2026-09-12) — SUPERSEDES our main claims
- **Pinned commits:**
  - HEAD b157f43fc0be4c59c3a517ec6464f27eaa72b8a0 (2026-09-18). The relevant files are unchanged since the first commit
    66514f4efef874280da5df34d6f747b6cf68029a (2026-09-12T22:05Z = 2026-09-13 07:05 JST).
  - Tag v0.1.0 → d0ed2c06bb3a9e7ed31e2f31e24d17de6323efe8.
- **Against the same official definitions:** their lean/AC.lean has sha256 927ba318…, identical to ours. Lean 4.29.1;
  axioms {propext, Classical.choice, Quot.sound}.
- **Family:** `presentation n a b c = (x⁻¹yⁿxy^{-(n+1)}, x⁻¹ y^a x y^b x⁻¹ y^c)` (lean/ACMillerSchupp.lean).
- **Proved:**
  - `shear_solvable_iff`: c is free (the shear x ↦ y^k x, a triviality transfer).
  - `ParameterShift.shift_steps`: an explicit path (a,b,c) → (a − nt, b + (n+1)t, c).
  - `a_period`: a has period n. `b_period`: b has period n+1.
  - `residue_solvable_iff`: triviality depends only on (a mod n, b mod n+1).
  - `zero_a_solvable`, `zero_b_solvable`; `uniform_family`: (n−1, 1, c) solvable for all n.
  - `YInversion.solution`: (a,b,c) ⇒ (−a,−b,−c).
  - `all_parameters_two` / `all_parameters_small`: every (a,b,c) for n ≤ 2.
  (All in lean/ACResidueClasses.lean, ACParameterShift.lean, ACUniformShearFamily.lean, ACYInversion.lean.)
- **Correspondence (ours, Lean):** `MS_wA_reach_SnPres : Reachable (MS n (wA m)) (SnPres n (-m) m 0)` in
  lean/ACProof/Comparison.lean (inversion plus one conjugation). SnPres restates their pair with our generators; we do not
  import their code.
- **Consequences (paper-level combination with their stated theorems, not re-checked in a joint Lean build):**
  - **n = 2 all m** (`MS2_wA_all`, `MS2_wA_all'`) follows from their `all_parameters_two` at (−m, m, 0). KNOWN.
  - **`MS_wA_cover`** follows:
    - m ∈ nℤ ⇒ a ≡ 0 (`zero_a_solvable`).
    - m ∈ (n+1)ℤ ⇒ b ≡ 0 (`zero_b_solvable`).
    - m ≡ 1 mod n(n+1) ⇒ (−1, 1) ≡ (n−1, 1) (`uniform_family`).
    - m ≡ −1 ⇒ y-inversion of the previous case.
    - Verdict: KNOWN (as a consequence; they do not state the wA family).
  - **Period (`MS_wA_period`):** the triviality consequence (depends only on m mod n(n+1)) follows from
    `residue_solvable_iff` via CRT. KNOWN at triviality level. Their periods are finer: independent periods n in a and
    n+1 in b on a 3-parameter family. Our statement is AC-equivalence of the two presentations (`Reachable` both ways),
    proved by one-relator conjugacy. Their a-period goes through the shear, so their stated theorems give only the
    triviality iff. The AC-equivalence refinement is the only part not literally covered; it is a minor refinement, and
    whether their path lemmas also give it was not checked.
  - **n = 3, 4 certified residues:** our solved residues map to their grid cells (a mod n, b mod n+1) by CRT.
    - Cells their stated theorems cover: a ≡ 0, b ≡ 0, (n−1, 1), (1, n). For n = 3 that is m ≡ 0,1,3,4,6,8,9,11 (mod 12);
      for n = 4, m ≡ 0,1,4,5,8,10,12,15,16,19 (mod 20).
    - **Cells only we certify** (by Lean-checked search paths): n = 3, m ≡ 2, 10 (cells (1,2), (2,2)); n = 4,
      m ≡ 2, 6, 14, 18 (cells (2,2), (2,1), (2,4), (2,3)).
    - I found none of these in their Lean files (`presentation 3`/`presentation 4` occur nowhere) or README. Their paper
      was only keyword-searched. Status: not found in the sources checked; finite instances (Fagan/Shehper benchmark
      tables may contain them).
  - **AK links:** in their coordinates, MS(3, wA 5) and MS(4, wA(−9)) are cell (1,1) at n = 3 and n = 4. Their repo has
    no AK(3)/AK(4) statement. The AK(3) link is known (Shehper v2 §3; Carreras Thm 4). The AK(4) link remains
    "novelty unconfirmed".
- Their PRIOR_WORK.md cites Shehper, Myasnikov, Lisitsa, Bridson, Panteleev–Ushakov, Lackenby, Zhang et al., Fagan et al.
  and Carreras, and disclaims novelty of substitution/automorphism techniques.

### B′. Correction (2026-10-21 JST): the published SAIR entry vs the repository
- **The entry:** SAIR ACC-P000002, Rob Sneiderman, "Explicit AC constructions for divisibility subfamilies of square
  presentations", https://competition.sair.foundation/contributor-network/acc/ACC-P000002.
  - Published 2026-09-13T00:19:51Z (09:19 JST). AC / proof / partial, versionId 2.
  - It has no commitHash and gives no repo link.
- **What it claims:** only results on G(p,s) = (u²y^{-(2s+1)}, u y^p u y^{-s} u⁻¹ y^{-p}): p | s or s+1, all G(2,s), and
  G(3,3m+1) reduced to an open restoration condition. Its stated claim does not imply our results.
- **Identifying the package:** github.com/Robby955/ac-square-divisibility tag v0.1.0
  = d0ed2c06bb3a9e7ed31e2f31e24d17de6323efe8, released 2026-09-12T23:58Z. The evidence:
  - the v0.1.0 paper title equals the entry title;
  - same G(p,s);
  - same SAIR pin 99a65377;
  - same 50/48 replay matrix;
  - the release came 21 minutes before publication.
- **The title I cited earlier** ("…for square presentations") is the README heading of the later v0.2.0-rc1 HEAD
  b157f43f.
- **Where the MS-family theorems live:** the P(n,a,b,c) theorems I relied on (`a_period`, `b_period`,
  `residue_solvable_iff`, `zero_*`, `uniform_family`, `YInversion.solution`, `all_parameters_two`) are in v0.1.0 with
  blobs identical to HEAD. They are built as part of the package (ACSquareFamily imports ACResidueClasses).
  - They are NOT stated in the entry text.
  - The v0.1.0 paper only defines P(n,a,b,c) and the dictionary to G(p,s). It says its height-3/4 consequences give
    "particular slices, not the full three-parameter families".
- **Corrected framing:** the implied-by analysis holds against the repository package behind ACC-P000002, not against
  the entry's stated claim.
- **Not done:** I have not built their package; that their modules compile is their claim.

### C. Lisitsa 2025 correction
- arXiv:2501.18601v1 (17 Jan 2025) abstract: AK(3) "is stably AC-equivalent to the trivial presentation".
- Published version: J. Comput. Algebra 16 (2025) 100041, doi:10.1016/j.jaca.2025.100041 (online 2025-10-15). Its
  abstract (via OpenAlex; ScienceDirect returned 403) says the claim it relied on "was based on an incorrect theorem, and
  thus the status of AK(3) remains unresolved". Shehper et al. v2 (L238–240) also report the MMS02 misprint.
- **Our manuscript does not use any stable-AC statement.** grep of draft_writeup.md, README.md and lean/ for "stabl"
  finds only the §2d disclaimer "any stable-AC statement" (no claim). The AK(3) link we cite is the ordinary
  AC-equivalence of Shehper v2 §3 / Carreras Thm 4, not the stable claim.

### D. Carreras / Fagan repositories
- **joe-carr-data/ac-certificates** @ d347fc4764ee55de6fc779fe697769127dde48e3: 0 .lean files. Python verifier
  (`ac_verify.py`), JSON certificates, Prover9 inputs.
- **Math-AI-Caltech/ACSolverX** @ 6a12515fe1d95178a483b76d5553266e61122417: 0 .lean files (JAX code, datasets).
- **No Lean formalizations in either repository.** Fagan et al. cite Zhang et al. 2025 as "Lean-based formal
  verification".

### Revised verdict table (supersedes the 2026-10-14 table below where they differ)
| Result | v1.1 verdict |
|---|---|
| `MS2_wA_all`, `MS2_wA_all'` (n=2 all m) | KNOWN: implied by Sneiderman `all_parameters_two` + our `MS_wA_reach_SnPres`; instances m=±1,±5 in Myasnikov 1999 / Havas–Ramsay 2003 |
| `MS_wA_cover`, `MS_wA_mult`, `MS_wA_mult_succ`, `MS_wA_pm_one` | KNOWN as consequences of Sneiderman's residue theorems |
| `MS_wA_period(_mul)` | triviality consequence KNOWN (Sneiderman `residue_solvable_iff`); the AC-equivalence-of-presentations form is a minor refinement, not found stated |
| `MS_wA_negate` | KNOWN principle (PU Lemma 3.1; Sneiderman `YInversion.solution`) |
| `MS3_wA` cells m≡2,10 (mod 12); `MS4_wA` cells m≡2,6,14,18 (mod 20) | not found in the sources checked (finite instances; possibly in benchmark data) |
| `MS3_wA5_iff_AK3` | KNOWN (Shehper v2 §3; Carreras Thm 4) |
| `MS4_wAm9_iff_AK4` | novelty unconfirmed |
| §2a re-formalizations | KNOWN mathematics; earlier formalization by George/Zhao in a different framework (repo unreleased) |

---

## Earlier record: novelty check (2026-10-14 JST) — AK(3) link and wA-family results

Method:
- **Citation lists:** Semantic Scholar API citation lists of Shehper et al. arXiv:2408.15332 (15 citing works), MMS
  arXiv:math/0302080 (29) and Panteleev–Ushakov arXiv:1609.00325 (10). A further Semantic Scholar query hit the API rate
  limit.
- **Full text read** (pdftotext, keyword search, then reading the relevant sections): 2607.23611, 2606.21611, 2608.18929,
  2606.06122, 2501.18601, 2304.03196; earlier: 2408.15332v2, math/0302080, 1609.00325.
- **Web searches:** wA family, AK(3)/MS equivalences, Lisitsa parametric work, Havas–Ramsay. Miller–Schupp 1999 was read
  from a web copy. No Google Scholar UI was used, so the search was not exhaustive.

Identity used below: by period plus reduction mod n (Lean `MS_wA_period_mul`, `MS_wA_reduce`, all AC-equivalences),
MS(3, wA 5) ~ MS(3, wA(−7)) ~ MS(3, y x y x⁻¹). The second relator x·(yxyx⁻¹)⁻¹ = x²y⁻¹x⁻¹y⁻¹ is a cyclic rotation of
x⁻¹y⁻¹x²y⁻¹, i.e. the relation x = y⁻¹x²y⁻¹. So **MS(3, wA 5) is AC-equivalent to the length-14 presentation
⟨x,y | x⁻¹y³x = y⁴, x = y⁻¹x²y⁻¹⟩** of Shehper et al. Likewise MS(4, wA(−9)) ~ MS(4, yxyx⁻¹).

## Sources checked
| Source | Content relevant here |
|---|---|
| Shehper et al., arXiv:2408.15332v2 (Feb 2025), §3 p.11 | Length-14 unsolved MS: the four presentations ⟨x,y \| x⁻¹y³x=y⁴, x=y^{±1}x²y^{±1}⟩ and ⟨x⁻¹y²x=y³, x=x⁻²y⁻¹x²y^{±1}⟩ are stated AC-equivalent to AK(3) (sequences not published). Thm 2/3/6/7, Cor 9: families MS(1,w), MS(n,w⋆), MS(n,w_k). No wA family, no period. |
| Carreras, arXiv:2607.23611v1 (Jul 2026), Thm 4 | **MS(3, y⁻¹x²y⁻¹) is AC-equivalent to AK(3)**: explicit certificate, 22 classical moves. Thm 3: MS(3, yx²y) ~ AK(3). Uses σ: y ↦ y⁻¹ (our ψ) to pair presentations, and cites Panteleev–Ushakov's realization of Aut(F₂) on AK(n). |
| Fagan, Tarquini, Shehper et al., "The Two-Hump Problem", arXiv:2606.21611v1 (Jun 2026), App. F, Tables 2–3 | Classifies the 1190-presentation MS benchmark (n ≤ 7, \|w\| ≤ 7). MS(3, yxyx⁻¹), MS(3, x⁻¹y⁻¹xy⁻¹), MS(3, y²xy⁻¹x⁻¹), … are in class 13₁, whose representative (y⁻¹x⁻¹yx⁻¹y⁻¹x, y⁻³x⁻⁴) is AK(3) up to symmetry. For n = 4, MS(4, yxyx⁻¹) etc. are in class 15₁ (length 15 = \|AK(4)\|); the text I read does not say explicitly that 15₁ is AK(4)'s class. Many reduced wA words appear as "trivial" for n = 2. |
| Panteleev–Ushakov, arXiv:1609.00325 (GCC 2019) | Lemma 3.1 (citing MMS Prop 1(iii) and earlier work): if automorphisms are allowed alongside AC-moves, AC-triviality is unchanged. This is the principle behind our transfers `MS_wA_negate` and `MS3_wA5_iff_AK3`. Prop 3.7 / Cor 3.8: φ(AK(n)) ~AC AK(n) for all φ ∈ Aut(F₂). Thm 2.3: AC-moves can replace a relator by a conjugate modulo the other relator (the mechanism behind our period theorem). Random MS(2,w) experiments only. |
| MMS, arXiv:math/0302080v1 | Prop 1.1 (AK(2)), Prop 1.3 (AK(n) ~ MS(n, w₁)). No wA family. |
| Lisitsa, Ex. Countex. 6 (2024) 100168; LPAR-2024 Compl. vol. 18, pp. 131–136; arXiv:2501.18601 | MS(n, w⋆) trivializations for n = 3..8 (later n = 9), and a stable trivialization of AK(3) by automated deduction. Notes that automorphisms preserve AC-triviality and cites PU for AK(n). No wA family, no period. |
| Havas–Ramsay, IJAC 13 (2003) 61–68 (web copy) | Trivializes the four length-12 MS(2, y^{±1}xy^{±1}x⁻¹), following Myasnikov 1999. These are reduced forms of wA(m), m ∈ {±1, ±5}, for n = 2: **specific instances of our n = 2 theorem are known.** |
| Miller–Schupp 1999 (web copy) | Defines the family and proves triviality. No AC results. |
| Lackenby, arXiv:2606.06122 | Stable AC and thickenable presentations; mentions MS(2, w) as examples and Nielsen automorphisms. No wA or AK-equivalence results. |
| McDermott, arXiv:2608.18929 | u-substitutions / automorphisms of presented groups. No MS/AK AC results. |
| Romary–Zupan, arXiv:2304.03196 | Trisection-based AC trivializations; uses automorphisms as an extended AC move. Unrelated families. |
| Not checked | Burns–Macedońska full text; Myasnikov 1999 tables; Havas–Ramsay data files; the GitHub datasets of Fagan et al. and Carreras (they may contain explicit MS(3, ·)/AK(3) links); the other citing papers (CayleyPy, RL papers). |

## Verdicts
| Result (Lean) | Verdict | Reason |
|---|---|---|
| `MS3_wA5_iff_AK3` / `MS3_wA_of_AK3` (MS(3, wA 5) AC-trivial ⇔ AK(3)) | **KNOWN** (stronger form) | MS(3, wA 5) ~ MS(3, y⁻¹x²y⁻¹ form), which Shehper et al. v2 state is AC-equivalent to AK(3), and Carreras 2026 Thm 4 certifies it with an explicit AC path. Fagan et al. 2026 class 13₁ also contains it. Ours is only a triviality transfer, weaker than their AC-equivalence. What remains ours: a short human-readable algebraic proof (automorphism x ↦ xy³ plus one BS(3,4) identity) and a Lean-kernel check against the official definitions. The method (automorphism transfer plus conjugation in the one-relator quotient) is standard (PU Lemma 3.1, Thm 2.3). |
| `MS4_wAm9_iff_AK4`, `MS4_wA_9_11_of_AK4` (n = 4, class {9, 11} mod 20) | **novelty unconfirmed; likely known as an unproved claim** | Fagan et al. put MS(4, yxyx⁻¹) (~ MS(4, wA(−9))) in class 15₁ alongside other words. Whether 15₁ is AK(4)'s class is not stated in the text I read; their dataset was not checked. I found no explicit AK(4) ↔ MS(4, ·) certificate. |
| `MS_wA_period` (period n(n+1), all n) | **novelty unconfirmed (weak evidence of novelty)** | No source states a periodicity in m for MS(n, y^{-m}xy^m x⁻¹). The mechanism (relator conjugate in BS(n,n+1) ⇒ AC-equivalent) is standard (PU Thm 2.3), so this is plausibly folklore-level. |
| `MS_wA_cover`, `MS_wA_mult`, `MS_wA_mult_succ`, `MS_wA_pm_one` | **novelty unconfirmed; corollary-level** | Short arguments from standard lemmas. Finitely many instances appear as "trivial" in the Shehper/Fagan benchmark tables. No infinite-family statement found. |
| `MS_wA_negate` (y ↦ y⁻¹ transfer) | **KNOWN principle** | Automorphism invariance of AC-triviality: PU Lemma 3.1 with its citations; Lisitsa 2025; Carreras 2026 uses the same σ. |
| `MS2_wA_all` / `MS2_wA_all'` (n = 2, all m) | **novelty unconfirmed; instances known** | The m ≡ ±1, ±5 instances (length 12) are in Myasnikov 1999 / Havas–Ramsay 2003, and benchmark instances are trivial in Shehper/Fagan. I found no statement for all m ∈ ℤ. |

**Recommended wording for the manuscript:**
- Present the AK(3) link as an independent formal proof of a known fact, citing Shehper et al. v2 §3 and Carreras 2026 Thm 4.
- Present the period and n = 2 all-m results as "not found in the literature checked", with the standard-technique caveat.
