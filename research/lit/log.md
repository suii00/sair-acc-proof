# log: sair-acc-v1.1-prior-art (times JST)

Method: imozuru skill (/workspace/imozuru/skills/imozuru). The skill calls for two parallel searcher subagents with
different approaches. This executor cannot launch subagents, so **I ran both approaches myself, one after the other**:
(A) term/keyword search (WebSearch, `gh search repos/code`); (B) citation/author chaining and venue scans (OpenAlex
`chain.py`, links inside the saved sources, the GitHub tree API).

## Round 0 (2026-10-20 ~03:20–03:55)
- A: WebSearch / WebFetch for the George blog → found https://www.robertj1.com/ai4science/ac-conjecture-aristotle/ (June
  2026). Its links: the research page anchor /research/#ac-formalization-paper, escholarship 6fm617h4, arXiv refs. No GitHub
  link.
- A: `gh search repos "Andrews-Curtis"` gave 26 repos. Relevant: SAIRcompetition/Andrews-Curtis, Robby955/ac-square-divisibility
  ("Explicit Andrews-Curtis constructions for divisibility subfamilies, with Lean proofs"), joe-carr-data/ac-certificates
  (Carreras artifact), alejandrozarco/andrews-curtis-ms14, Amey-Thakur/SAIR-ANDREWS-CURTIS-CHALLENGE, ph4ge/ac-detour-width,
  plus search/RL repos. No repo by George/Zhao.
- A: `gh search code` (language lean) for "Akbulut": TauCeti, facebookresearch/atlas-lean (topology wanted-lists). Not
  relevant. For "Reachable" "standard 2": only our own private repo is indexed (code search covers default branches only).
- B: GitHub tree API .lean counts: ac-certificates 0, ACSolverX 0, Amey-Thakur 0, alejandrozarco 0, nahomar 0,
  HrushikeshPawar 0, NullLabTests 0, git-df-scott 0, ElliotSteffen 0, ph4ge 2 (AC.lean, DetourWidth.lean),
  Robby955 ~30 files.
- **Decisive find (B):** Robby955/ac-square-divisibility (Robert Sneiderman). Public since 2026-09-12 (repo created
  2026-09-12T23:51Z; commit 66514f4e 2026-09-12T22:05Z holds ACResidueClasses/ACParameterShift/ACMillerSchupp; tag v0.1.0
  → d0ed2c06, 2026-09-12T23:32Z; HEAD b157f43f 2026-09-18). Its lean/AC.lean has sha256 927ba318…, byte-identical to our
  pinned official AC.lean. It proves periods and the full n ≤ 2 case for the three-parameter MS family
  (x⁻¹yⁿxy^{-(n+1)}, x⁻¹y^a x y^b x⁻¹ y^c).

## Round 1 (2026-10-20 ~03:55–04:05)
- fetch.py OK: George blog, George research page, Lisitsa arXiv abs + pdf, Sneiderman README / PRIOR_WORK / 5 Lean files
  (pinned to commit b157f43f), Carreras pdf + repo README (d347fc47), Fagan pdf + ACSolverX README (6a12515f), Shehper v2 pdf.
- fetch.py FAIL: ScienceDirect S2772827725000129 (HTTP 403) and OpenReview lt3Lpa4d2d (415 characters, bot page).
  Fallback for Lisitsa: the OpenAlex record W4415219113 (abstract_inverted_index reconstructed by script, verbatim word
  order). Crossref confirms J. Comput. Algebra vol 16, article 100041, Dec 2025.
- Chaining:
  - `chain.py find 10.48550/arxiv.2408.15332` → W4402705686.
  - `chain.py cites` → 3 works: Lisitsa Exco 2025 (MS_9(w⋆), 8634 moves), Fagan 2026 "RL lessons", an unrelated ICMLT
    paper. No wA/period content in the abstracts (saved as openalex-*.md).
  - `chain.py author "Robert Joseph George"` → wrong person (Daniel D. Koleske); this is the documented same-name weakness.
  - Backward from the Carreras pdf (L48, L423) → repo; from the Fagan pdf (L59) → ACSolverX.
- Saturation is not counted: the two approaches were run by one agent, sequentially. Every required claim C0–C5 now has a
  file:line location, so I stopped under the rule "every required claim has a source location". C6 (technique origin)
  rests on the earlier round's /tmp copies; not re-fetched.

## Decisions
- The Sneiderman find changes the v1.1 narrative. The user's plan labelled period / MS_wA_cover / n=2 all m "not found in
  literature checked". That label is now false: their triviality content follows from Sneiderman's public Lean theorems
  (2026-09-12) plus our 2-step correspondence `MS_wA_reach_SnPres` (lean/ACProof/Comparison.lean). The writeup was revised
  accordingly (see NOVELTY.md §v1.1).
- No background processes left from this research (the Lean build and reproduce run are separate; see the build logs).

## Feedback from the user (verbatim, to be appended when given)
