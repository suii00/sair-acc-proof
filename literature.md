# Literature survey (ACC Proof Track) — compiled 2026-10-13
Status column: [V]=metadata confirmed by web search (2026-10-13); [M]=from memory, still unverified.

| # | Authors | Title / venue | URL | Key results (theorem numbers where known) | St |
|---|---|---|---|---|---|
| 1 | J.J. Andrews, M.L. Curtis | Free groups and handlebodies, Proc. AMS 16 (1965) 192–195 | https://doi.org/10.1090/S0002-9939-1965-0173241-8 | Origin of the conjecture | V |
| 2 | S. Akbulut, R. Kirby | A potential smooth counterexample in dimension 4 to the Poincaré conjecture, the Schoenflies conjecture, and the Andrews–Curtis conjecture, Topology 24 (1985) 375–390 | https://doi.org/10.1016/0040-9383(85)90010-2 | AK(n)=<x,y|x^n=y^{n+1}, xyx=yxy> | V (AK(2) attribution to Gersten: M) |
| 3 | C.F. Miller III, P.E. Schupp | Some presentations of the trivial group, Contemp. Math. 250 (1999) 113–115 | MR1732210 | MS(n,w)=<x,y|x^-1 y^n x=y^{n+1}, x=w>, w with x-exponent-sum 0, presents trivial group | V |
| 4 | R.G. Burns, O. Macedonska | Balanced presentations of the trivial group, Bull. LMS 25 (1993) 513–526 | https://doi.org/10.1112/blms/25.6.513 | Survey of balanced presentations of the trivial group (MR1245076) | V |
| 5 | A.D. Myasnikov | Genetic algorithms and the Andrews–Curtis conjecture, IJAC 9 (1999) 671–686 | https://doi.org/10.1142/S0218196799000370 | Computer search; trivialized many short presentations | V (vol/pages via citation) |
| 6 | A.D. Myasnikov, A.G. Myasnikov, V. Shpilrain | On the Andrews–Curtis equivalence, Contemp. Math. 296 (2002) 183–198 | arXiv:math/0302080 | AK(n) AC-equivalent to MS(n, y^-1x^-1yxy) (=Prop. 5 in Shehper v2); p.10 misprint per Shehper v2 | V |
| 7 | G. Havas, C. Ramsay | Breadth-first search and the Andrews–Curtis conjecture, IJAC 13 (2003) | https://doi.org/10.1142/S0218196703001365 | IJAC 13(1):61–68. Length ≤12 AC-trivial (also Myasnikov/MAGNUS) | V |
| 8 | M.R. Bridson | The complexity of balanced presentations and the Andrews–Curtis conjecture (2015) | arXiv:1504.04187 | AC-trivial presentations needing superexponentially (tower) many moves | V (via citation) |
| 9 | B. Lishak | Balanced finite presentations of the trivial group, J. Topol. Anal. (2017) | arXiv:1504.00418 | Independent superexponential lower bounds | V (via citation) |
| 10 | A. Lisitsa | First-order theorem proving in the exploration of Andrews–Curtis conjecture (2018); Stable AC trivialization of AK(3) revisited (2024) | (2018 arXiv id NOT recorded; not cited in manuscript) | Automated deduction (Prover9) AC sequences; alt. stable trivialization of AK(3) | V (2024 paper) |
| 11 | D. Panteleev, A. Ushakov | Conjugacy search problem and the Andrews–Curtis conjecture, Groups Complex. Cryptol. (2019) | arXiv:1609.00325 (corrected) | ACM-moves, automorphism moves; failed to trivialize AK(n), n>2 | V |
| 12 | A. Shehper, A. Medina-Mardones, et al., S. Gukov | What makes math problems hard for reinforcement learning: a case study (NeurIPS 2025) | https://arxiv.org/abs/2408.15332 | Thm A: MS(1,w) ∀w; MS(n, y^-1xyx^-1) ∀n; MS(2, y^-k x^-1yxy) ∀k are AC-trivial. Thm B: AK(n) length-reducible (n≥2). v1 AK(3) stable claim retracted in v2 (MMS misprint) | V |
| 13 | S.M. Gersten | On Rapaport's example in presentations of the trivial group (preprint, 1987) | — | AK(2) trivialization; Rapaport-type examples | M |
| 14 | S.V. Ivanov | On balanced presentations of the trivial group, Invent. Math. 165 (2006) 525–549 | https://doi.org/10.1007/s00222-005-0496-1 | CORRECTED: answers Magnus's question negatively (balanced trivial presentation where no relator can be swapped for a generator); DOI 10.1007/s00222-005-0497-1. Also Ivanov, PAMS 134 (2006) 1561–1567: cyclic AC ⇔ stable AC | V |
| 15 | I. Bobrowski? / Metzler, Hog-Angeloni (survey) | "Two-dimensional homotopy and combinatorial group theory", LMS LN 197 (1993), ch. on AC | — | Standard survey; stable AC ↔ 3-deformations of 2-complexes | M |

Existing formal proofs in official repo (commit a0fd6e6f): only AC.lean — definitions, `not_conjecture_iff_counterexample`,
`Reachable.stable`, `Conjecture.stable`, `StableCounterexample.counterexample`. No AC-triviality theorems formalized.

Additional (found 2026-10-13):
- A. Lisitsa, New Andrews–Curtis trivializations for Miller–Schupp group presentations, Examples & Counterexamples 6 (2024) 100168 [V via citation].
- Thickenable presentations & stable AC with explicit move bounds, arXiv:2606.06122 (2026) [V, authors not recorded].
- Andrews–Curtis groups, arXiv:2506.23031 [V title only].
- Hog-Angeloni, Metzler, The Andrews–Curtis conjecture and its generalizations, LMS LN 197 (1993) 365–380 [V].
- Lishak arXiv number (1504.00418) still UNVERIFIED; Gersten preprint UNVERIFIED.
- Shehper et al. v2 numbering: abstract-level "Theorem B" (i)-(iii) = main-text Theorem 2, Theorem 3, Corollary 9. Cor. 9 relies on AK(2) AC-triviality + MMS Prop. 5 + Theorem 6.

**v1 note (2026-10-13):** the manuscript (`draft_writeup.md` §5) cites only the verified entries [AC], [MiS], [AK], [MMS], [SMF] and the
official repo, with theorem numbers checked against arXiv:2408.15332v2 and arXiv:math/0302080v1. [M] entries (Gersten, Lishak id,
Hog-Angeloni/Metzler survey) and the Lisitsa 2018 item are NOT cited.
