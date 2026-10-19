# map: sair-acc-v1.1-prior-art

Question: For our Lean results on MS(n, y^{-m}xy^m x⁻¹) and the AK(3)/AK(4) links, what has already been formalized or
stated? By whom, against which definitions, and where is the source (URL/section/commit)?
First search terms: "Formalizing the Andrews-Curtis conjecture" George Aristotle; "Andrews-Curtis" Lean GitHub;
"Stable AK(3) revisited".

## Required claims
- [x] C0 Venues: where AC formalization and prior art is published — blogs (robertj1.com), arXiv, OpenReview (NeurIPS
  MATH-AI), GitHub (SAIR participants' repos), journals (J. Comput. Algebra, Ex. Countex.). See the Venues section.
- [x] C1 What George/Zhao formalized, against which definitions, and whether the repo is public —
  sources/george-2026-formalizing-ac-aristotle.md L172 "fully formalized the mathematical results", L177 "plan to release
  the full repository soon", L251 "inductive ACMove : Presentation (Fin 2)", L400 "theorem AK_equiv_MS_w₁", L668
  "was not a constructor".
- [x] C2 Is anything equivalent to our period / cover / n=2 results already in Lean against the official AC.lean? —
  sources/sneiderman-2026-ACResidueClasses.md L53-55 `a_period`, L71-73 `b_period`, L139-140 `all_parameters_two`;
  sneiderman-2026-ACUniformShearFamily.md L187-188 `uniform_family`; sneiderman-2026-ACMillerSchupp.md L24 `def second`;
  sneiderman-2026-readme.md L108 "pinned to SAIR commit 99a65377".
- [x] C3 Lisitsa 2025 correction (stable AK(3) claim withdrawn) — sources/lisitsa-2025-jca-abstract-openalex.md L9
  "status of AK ( 3 ) remains unresolved"; arxiv-2501.18601-lisitsa-stable-ak3.md L16 (original claim);
  arxiv-2408.15332-shehper-v2.txt L238-240 "subtle misprint".
- [x] C4 AK(3) ~ MS(3, ·) is already stated or certified — arxiv-2408.15332-shehper-v2.txt L536-537;
  arxiv-2607.23611-carreras-length14.txt L200 "Theorem 4".
- [x] C5 Lean in the Carreras and Fagan repos? — none (GitHub tree API: 0 .lean files). carreras-ac-certificates-readme.md
  L18 (Python verifier); acsolverx-readme.md L13 "JAX-based"; arxiv-2606.21611-fagan-two-hump.txt L87 (cites Zhang et
  al. 2025 Lean work).
- [ ] C6 The original source of the technique (automorphism transfer / conjugacy modulo a relator) — Panteleev–Ushakov
  arXiv:1609.00325 Lemma 3.1 / Thm 2.3 (read in round 2025-10-14; copy in /tmp/nov, not re-fetched into sources/ this round).

## Terms
- AC-equivalence via `Relation.EqvGen ACMove` (George) vs `ReflTransGen Step` (SAIR `AC.Reachable`) — george…md L263; official AC.lean
- "solvable" = `Reachable P (standard 2)` (Sneiderman) — sneiderman-2026-ACResidueClasses.md
- "shear" x ↦ y^k x (Sneiderman) ≈ our phiK — sneiderman-2026-ACMillerSchupp.md L28
- "power-conjugate criterion", "witness" (product of conjugates of first relator) — sneiderman-2026-ACMillerSchupp* files

## People
- Robert Joseph George (Caltech, Anandkumar group) — AC formalization blog (2026), NeurIPS 2025 MATH-AI poster
- Aaron Zhao (blog L42) / "Aaron Zhou" (OpenReview author list as quoted in Sneiderman PRIOR_WORK; not verified)
- Robert Sneiderman (independent; GitHub Robby955) — ac-square-divisibility (Lean, SAIR AC.lean)
- Josep Carreras (GitHub joe-carr-data) — arXiv:2607.23611, ac-certificates
- Lucas Fagan, Ali Shehper, Sergei Gukov (Caltech) — Two-Hump / ACSolverX; Shehper et al. 2408.15332
- Alexei Lisitsa (Liverpool) — ATP AC trivializations; stable AK(3) correction

## Venues
- robertj1.com/ai4science — https://www.robertj1.com/ai4science/ac-conjecture-aristotle/
- OpenReview NeurIPS 2025 MATH-AI — https://openreview.net/forum?id=lt3Lpa4d2d
- GitHub search "Andrews-Curtis" (SAIR participant repos) — https://github.com/search?q=Andrews-Curtis&type=repositories
- arXiv math.GR / cs.LG
- Journal of Computational Algebra; Examples and Counterexamples (Elsevier)

## Sources (sources/, gitignored)
| Paper / material | File | Original URL | Where it came from (round, move) |
|---|---|---|---|
| 〔本人〕George 2026 blog | george-2026-formalizing-ac-aristotle.md | https://www.robertj1.com/ai4science/ac-conjecture-aristotle/ | R0 term search |
| 〔本人〕George research page | george-research-page.md | https://www.robertj1.com/research/ | R1 author |
| 〔本人〕Sneiderman README, PRIOR_WORK, 5 Lean files @ b157f43f | sneiderman-2026-*.md | https://github.com/Robby955/ac-square-divisibility | R0 GitHub venue scan |
| 〔論文〕Lisitsa arXiv:2501.18601 abs + pdf | arxiv-2501.18601-lisitsa-stable-ak3.md, arxiv-2501.18601-lisitsa-pdf.txt | https://arxiv.org/abs/2501.18601 | R0 |
| 〔論文〕Lisitsa JCA 16 (2025) 100041, abstract via OpenAlex | lisitsa-2025-jca-abstract-openalex.md | https://doi.org/10.1016/j.jaca.2025.100041 | R1 (ScienceDirect 403) |
| 〔論文〕Carreras arXiv:2607.23611 | arxiv-2607.23611-carreras-length14.txt | https://arxiv.org/pdf/2607.23611 | R0 |
| 〔本人〕Carreras repo README @ d347fc47 | carreras-ac-certificates-readme.md | https://github.com/joe-carr-data/ac-certificates | R1 backward (paper L48) |
| 〔論文〕Fagan et al. arXiv:2606.21611 | arxiv-2606.21611-fagan-two-hump.txt | https://arxiv.org/pdf/2606.21611 | R0 |
| 〔本人〕ACSolverX README @ 6a12515f | acsolverx-readme.md | https://github.com/Math-AI-Caltech/ACSolverX | R1 backward (paper L59) |
| 〔論文〕Shehper et al. arXiv:2408.15332v2 | arxiv-2408.15332-shehper-v2.txt | https://arxiv.org/pdf/2408.15332v2 | R0 |
| 〔論文〕Lisitsa Exco 2025 MS_9 (abstract, OpenAlex) | openalex-W4414420004.md | https://doi.org/10.1016/j.exco.2025.100201 | R1 forward (cites of Shehper) |
| 〔論文〕Fagan 2026 RL lessons (abstract, OpenAlex) | openalex-W7203992009.md | https://doi.org/10.1142/s3082883x26400035 | R1 forward (cites of Shehper) |

## Next leads
- George/Zhao repository once released — direct comparison of their MS families (their blog claims all of 2408.15332).
- OpenReview lt3Lpa4d2d full text — blocked by a bot check; needs the user's browser.
- Sneiderman paper/main.tex and research supplements — does any n = 3/4 grid cell (a mod n, b mod n+1) appear?
- Other SAIR proof-track repos (Amey-Thakur, ph4ge DetourWidth.lean, alejandrozarco) — scanned for .lean only.
