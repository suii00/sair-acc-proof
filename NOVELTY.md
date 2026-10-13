# Novelty check (2026-10-14 JST) — AK(3) link and wA-family results

> Note: the AK(3)/AK(4) Lean files (`AK3Link.lean`, `AK4Link.lean`) live on branch `research/n3-m5`, not in submission-v1.
> This file is a post-v1 record; the `submission-v1` tag is unchanged.

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
