# SAIR ACC Proof Track — "Create Submission" form draft (v1.1.2)

**Status: DRAFT. Not submitted.** Repo suii00/sair-acc-proof is public (the user approved this).
- Submission commit: tag `submission-v1.1.2` (the commit containing this file; its SHA is recorded in README). It is v1.1.1 with documentation-only fixes (Panteleev initial, Use of AI section). v1.1.1 was v1.1 plus the Apache-2.0
  LICENSE (PR #1).
- The tagged tree contains this form file and the final description. Tags submission-v1, v1.1, v1.1.1 were not moved.

## Title
Lean-verified AC-triviality for Miller–Schupp MS(n, y^-m x y^m x^-1): period, n=2, partial n=3,4, AK links

## Authors (one per line, ≤ 100 chars each)
Hideto Iitsuka

> ⚠ PLACEHOLDER — confirm the name, spelling and order, and whether to add an affiliation. AI assistance is disclosed in the
> Description.

## Claim type
**AC conjecture — proof** (recommended). These are ordinary-move AC-trivializations, AC-equivalences and AC-triviality
transfers. There is no stable-AC statement and no counterexample.

## Result completeness
**Partial result** (recommended).

## Description (Markdown + math; 9613 / 10,000 characters)
Source file: `submission/description_v1.1.md`; checked with `submission/check_length.py`.

## Claim

This is a **partial result** toward the Andrews–Curtis (AC) conjecture. It is **not** a proof of the conjecture. We give Lean 4 kernel-checked AC-trivializations and AC-equivalences for the Miller–Schupp family
$$\mathrm{MS}(n,\,w_A(m)) = \langle x,y \mid x^{-1}y^{n}x = y^{n+1},\ x = y^{-m}xy^{m}x^{-1}\rangle,$$
all stated directly against the **unmodified official** `AC.lean` (`AC.Reachable`, `AC.standard`). Much of the triviality content is already implied by prior Lean work (see *Contribution*). We separate what is independent re-verification, what is implied by others, and what may be new.

## Results (all Lean-checked)

1. **Period (all $n$).** $\mathrm{MS}(n,w_A(m))$ and $\mathrm{MS}(n,w_A(m+t\,n(n+1)))$ are AC-equivalent *presentations*: there is an AC path between them (`MS_wA_period_mul`).
2. **Families (all $n$).** $\mathrm{MS}(n,w_A(m))$ is AC-trivial for $m \in n\mathbb Z \cup (n+1)\mathbb Z \cup (\pm1+n(n+1)\mathbb Z)$ (`MS_wA_cover`).
3. **$n=2$, all $m\in\mathbb Z$.** AC-trivial (`MS2_wA_all'`, with an alternative proof `MS2_wA_all`).
4. **$n=3$:** AC-trivial unless $m\equiv\pm5 \pmod{12}$ (`MS3_wA`). **$n=4$:** AC-trivial unless $m\equiv\pm3,\pm7,\pm9 \pmod{20}$ (`MS4_wA`). The base cases are explicit search paths; each move is replayed as one official `Step`.
5. **AK links (AC-triviality transfers, not paths).**
   - $\mathrm{MS}(3,w_A(5))$ is AC-trivial iff $\mathrm{AK}(3)$ is (`MS3_wA5_iff_AK3`). Hence AK(3) AC-trivial ⇒ every $\mathrm{MS}(3,w_A(m))$ is (`MS3_wA_of_AK3`).
   - $\mathrm{MS}(4,w_A(-9))$ is AC-trivial iff $\mathrm{AK}(4)$ is (`MS4_wAm9_iff_AK4`). Hence AK(4) AC-trivial ⇒ the classes $m\equiv 9,11 \pmod{20}$ (`MS4_wA_9_11_of_AK4`).
6. **Comparison bridge.** $\mathrm{MS}(n,w_A(m))$ is AC-equivalent, by one inversion and one conjugation, to the point $(a,b,c)=(-m,m,0)$ of the three-parameter family $P(n,a,b,c)=(x^{-1}y^nxy^{-(n+1)},\ x^{-1}y^axy^bx^{-1}y^c)$ used in Sneiderman's package (`MS_wA_reach_SnPres`).
7. **Re-formalized known results.** MS(1,w), MS(n,w⋆), the $w_k$ equivalences, MS(2,$w_k$), AK(n) ~ MS(n,$w_1$), AK(2), MS(n,$w_k$) ~ P(n,k) (Shehper et al.; Myasnikov–Myasnikov–Shpilrain). Also invariance lemmas: AC moves preserve the normal closure; `Reachable` is symmetric; endomorphism transport.

## Argument (outline)

Let $G=F(x,y)/\langle\langle r_0\rangle\rangle$ with $r_0=x^{-1}y^nxy^{-(n+1)}$. Two facts are formalized:
- (`reach_slot1_mod`) if the image of $r_1'$ in $G$ is conjugate to the image of $r_1$, then $(r_0,r_1)\sim(r_0,r_1')$;
- (`Reachable.map`) an automorphism applied to every move transports AC-triviality.

**Period.** In $G$, $xy^{(n+1)k}x^{-1}=y^{nk}$. Put $N=n(n+1)$. Then $r_1(m+N)$ and $y^{n^2}r_1(m)y^{-n^2}$ both reduce to $xD_my^{m+n}$, where $D_m=xy^{-m}x^{-1}$. This uses that $y^N$ and $D_m$ commute, since both are $x(\text{power of }y)x^{-1}$.

**Families.** For $m\in n\mathbb Z$ or $(n+1)\mathbb Z$, the second relator reduces modulo $r_0$ to $x\,y^{q}$ up to conjugacy, followed by a substitution $x\mapsto y^{-q}$. For $m\equiv1$, use the period and $w_\star$ (Shehper et al., Thm 3). For $m\equiv-1$, use the automorphism $y\mapsto y^{-1}$.

**AK links.** The automorphism $x\mapsto xy^{k}$ ($k=3$, resp. $-6$) plus one Baumslag–Solitar identity sends $\mathrm{MS}(3,w_A(5))$ to $\mathrm{MS}(3,w_8)$, resp. $\mathrm{MS}(4,w_A(-9))$ to $\mathrm{MS}(4,w_{-9})$. Then $w_k$-equivalence and AK(n) ~ MS(n,$w_1$) finish the argument.

**$n=3,4$ bases.** Paths found by greedy search, emitted move by move, and checked in Lean.

Full paper proofs are in `draft_writeup.md` §3–4.

## Lean verification

- **Official statement:** SAIRcompetition/Andrews-Curtis @ `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e`, `competition/tools/lean/AC.lean` unmodified (sha256 `927ba318d26b06c312140117b2a4856373832ed2c043944f520ec7337bcfca1b`). Lean 4.29.1, Mathlib `5e932f97`.
- **Build:** the official lakefile has `warningAsError = true`. There is no `sorry`, `admit` or `native_decide`.
- **Axioms:** `#print axioms` was run on **59** theorems (`lean/ACProof/Check.lean`). All depend only on axioms from {`propext`, `Classical.choice`, `Quot.sound`}. 57 use exactly these three; `bs_pow` uses [`propext`]; `link_identity` uses [`propext`, `Quot.sound`].
- **Reproduction:** `scripts/reproduce.sh` clones the official repo at the pinned commit and checks the sha256. It copies `lean/ACProof/` alongside, adds one `[[lean_lib]]` entry, builds, scans for sorry/admit, audits axioms, and prints `REPRODUCE OK`.
- **Log:** a fresh-clone run is saved in `logs/build_axioms_v1.1_3ff15e7.log`. It ran on commit 3ff15e7. The submitted commit (tag `submission-v1.1.2`) has identical `lean/` and `scripts/`; it differs only in documentation.

## Contribution and prior work (honest scope)

- **Implied by prior work — in the repository behind SAIR ACC-P000002, not in that entry's stated claim.**
  - **The published entry.** Rob Sneiderman, *Explicit AC constructions for divisibility subfamilies of square presentations*, SAIR ACC-P000002 (https://competition.sair.foundation/contributor-network/acc/ACC-P000002, published 2026-09-13). It claims explicit AC constructions for the square family $G(p,s)=(u^2y^{-(2s+1)},\ uy^puy^{-s}u^{-1}y^{-p})$ when $p\mid s$ or $p\mid s+1$. **Its stated claim is a different family and does not imply our results.**
  - **Identifying the repository.** The entry lists no repository or commit. We identify its package as github.com/Robby955/ac-square-divisibility, tag v0.1.0 (commit `d0ed2c06bb3a9e7ed31e2f31e24d17de6323efe8`), on this evidence:
    - the paper title is the same;
    - the same $G(p,s)$ family;
    - the same SAIR definition pin;
    - the same 50/48 replay matrix;
    - the release came 21 minutes before the entry was published.
  - **Auxiliary Lean modules in that package.** It is built against the same official `AC.lean` and contains Lean modules on $P(n,a,b,c)$ that neither the entry nor its paper states as results: `a_period`, `b_period`, `residue_solvable_iff`, `zero_a_solvable`, `zero_b_solvable`, `uniform_family`, `YInversion.solution` and `all_parameters_two` (the files are unchanged at the current HEAD `b157f43f`).
  - **What follows for us.** With our bridge (item 6), these modules imply the AC-triviality content of items 2 and 3, and of item 1 at the level of triviality.
  - **How far this was checked.** This is a paper argument across two repositories. We read their statements but did not build their package or compile the combination.
  - Our proofs were developed independently, but we claim **no priority** for these statements.
  - The instances $m=\pm1,\pm5$ at $n=2$ are due to Myasnikov (1999) and Havas–Ramsay (2003).
- **Known facts, independently formalized.**
  - The AK(3) link: Shehper et al. (arXiv:2408.15332v2, §3) state that MS(3, ·) presentations of this form are AC-equivalent to AK(3). Carreras (arXiv:2607.23611, Thm 4) certifies this with an explicit path. Fagan et al. (arXiv:2606.21611, App. F) place it in AK(3)'s class.
  - The re-formalized results in item 7. George and Zhao report an earlier Lean formalization of the Shehper et al. results, in their own framework (not the official `AC.lean`). Their repository is announced but not released.
  - The techniques are standard: automorphism invariance and conjugacy modulo a relator (Panteleev–Ushakov, Lemma 3.1, Thm 2.3).
- **Possibly new (not found in the sources we checked; novelty not confirmed):**
  - the AC-equivalence-of-presentations form of the period (the a-period in that package passes through a triviality transfer);
  - certified classes $m\equiv2,10 \pmod{12}$ at $n=3$ and $m\equiv2,6,14,18 \pmod{20}$ at $n=4$, which the theorems in that package do not cover;
  - the AK(4) link `MS4_wAm9_iff_AK4`;
  - the Lean bridge `MS_wA_reach_SnPres` itself.
  - Benchmark datasets we did not inspect (Fagan et al., Carreras) may contain the finite classes.
- **Stable AC:** no stable-AC statement is made or used. The stable AK(3) claim of Lisitsa (arXiv v1) was withdrawn in the published version (J. Comput. Algebra 16 (2025) 100041).

## What remains unresolved

- $\mathrm{MS}(3,w_A(m))$ for $m\equiv\pm5 \pmod{12}$. Its AC-triviality is equivalent to that of AK(3).
- $\mathrm{MS}(4,w_A(m))$ for $m\equiv\pm3,\pm7 \pmod{20}$, and for $m\equiv\pm9$ (equivalent to AK(4)).
- $\mathrm{MS}(n,w_A(m))$ for $n\ge5$ outside item 2.
- AK(n) for $n\ge3$, and the AC conjecture itself.
- Our searches on the open classes failed (up to ~10M states). This is **not** evidence of non-triviality.

## AI assistance

The Lean proofs, the search scripts and the drafting of this text were developed with an AI assistant, under the author's supervision. The literature check also used it. Correctness rests on the Lean kernel check against the official definitions, reproducible with `scripts/reproduce.sh`; it does not rest on the assistant.

## References

Andrews–Curtis (1965); Akbulut–Kirby (1985); Miller–Schupp (1999); Myasnikov (1999); Myasnikov–Myasnikov–Shpilrain (2002, arXiv:math/0302080); Havas–Ramsay (2003); Panteleev–Ushakov (arXiv:1609.00325); Shehper et al. (arXiv:2408.15332v2); Lisitsa, J. Comput. Algebra 16 (2025) 100041; Fagan et al. (arXiv:2606.21611); Carreras (arXiv:2607.23611); R.J. George, "Formalizing the Andrews–Curtis conjecture" (blog, 2026); R. Sneiderman, SAIR ACC-P000002 (https://competition.sair.foundation/contributor-network/acc/ACC-P000002), package github.com/Robby955/ac-square-divisibility @ v0.1.0. Detailed record: `NOVELTY.md`, `research/lit/`.

## GitHub (optional)
- Repository link: https://github.com/suii00/sair-acc-proof
- Commit SHA (40 chars): the commit tagged `submission-v1.1.2` (see README for the full SHA)

## arXiv / Paper link (optional)
(leave empty)

## References — "Select one published ACC result that this submission builds on"
Recommendation: **ACC-P000002** — Rob Sneiderman, "Explicit AC constructions for divisibility subfamilies of square
presentations", https://competition.sair.foundation/contributor-network/acc/ACC-P000002
- It is the closest published ACC result, and the Description compares with it explicitly.
- Caveat: our proofs were developed independently and do not use its results. "Builds on" is loose here; the relationship
  is "overlapping prior work". If the form's wording should be read strictly, leaving the selector empty is also
  defensible.
