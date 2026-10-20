# SAIR ACC Proof Track — "Create Submission" form draft (v1.1)

Based on tag `submission-v1.1` → commit `4a5644e73f945b7a14ea85d9660a6240baec4ac6` (private repo suii00/sair-acc-proof).
**Status: DRAFT. Not submitted.** The repo visibility is unchanged (private).

## Title
Lean-verified AC-triviality for Miller–Schupp MS(n, y^-m x y^m x^-1): period, n=2, partial n=3,4, AK links

## Authors (one per line, ≤ 100 chars each)
Hideto Iitsuka

> ⚠ PLACEHOLDER — confirm the name, spelling and order, and whether to add an affiliation. AI assistance is disclosed in the
> Description, not listed as an author.

## Claim type
**AC conjecture — proof** (recommended).
Rationale:
- The results are AC-trivializations, AC-equivalences and AC-triviality transfers for ordinary AC moves.
- No stable-AC statement is made.
- No counterexample is claimed.

## Result completeness
**Partial result** (recommended). The full conjecture is not addressed, and several residue classes remain open (see
Description).

## Description (Markdown + math; 8207 / 10,000 characters)
Source file: `submission/description_v1.1.md`. Character count verified with `submission/check_length.py`.

## Claim

This is a **partial result** toward the Andrews–Curtis (AC) conjecture. It is **not** a proof of the conjecture. We give Lean 4 kernel-checked AC-trivializations and AC-equivalences for the Miller–Schupp family
$$\mathrm{MS}(n,\,w_A(m)) = \langle x,y \mid x^{-1}y^{n}x = y^{n+1},\ x = y^{-m}xy^{m}x^{-1}\rangle,$$
all stated directly against the **unmodified official** `AC.lean` (`AC.Reachable`, `AC.standard`). Much of the triviality content is already implied by prior work (see *Contribution*). We separate what is independent re-verification, what is implied by others, and what may be new.

## Results (all Lean-checked)

1. **Period (all $n$).** $\mathrm{MS}(n,w_A(m))$ and $\mathrm{MS}(n,w_A(m+t\,n(n+1)))$ are AC-equivalent *presentations*: there is an AC path between them (`MS_wA_period_mul`).
2. **Families (all $n$).** $\mathrm{MS}(n,w_A(m))$ is AC-trivial for $m \in n\mathbb Z \cup (n+1)\mathbb Z \cup (\pm1+n(n+1)\mathbb Z)$ (`MS_wA_cover`).
3. **$n=2$, all $m\in\mathbb Z$.** AC-trivial (`MS2_wA_all'`, with an alternative proof `MS2_wA_all`).
4. **$n=3$:** AC-trivial unless $m\equiv\pm5 \pmod{12}$ (`MS3_wA`). **$n=4$:** AC-trivial unless $m\equiv\pm3,\pm7,\pm9 \pmod{20}$ (`MS4_wA`). The base cases are explicit search paths; each move is replayed as one official `Step`.
5. **AK links (AC-triviality transfers, not paths).**
   - $\mathrm{MS}(3,w_A(5))$ is AC-trivial iff $\mathrm{AK}(3)$ is (`MS3_wA5_iff_AK3`). Hence AK(3) AC-trivial ⇒ every $\mathrm{MS}(3,w_A(m))$ is (`MS3_wA_of_AK3`).
   - $\mathrm{MS}(4,w_A(-9))$ is AC-trivial iff $\mathrm{AK}(4)$ is (`MS4_wAm9_iff_AK4`). Hence AK(4) AC-trivial ⇒ the classes $m\equiv 9,11 \pmod{20}$ (`MS4_wA_9_11_of_AK4`).
6. **Comparison bridge.** $\mathrm{MS}(n,w_A(m))$ is AC-equivalent, by one inversion and one conjugation, to the point $(a,b,c)=(-m,m,0)$ of Sneiderman's three-parameter family $(x^{-1}y^nxy^{-(n+1)},\ x^{-1}y^axy^bx^{-1}y^c)$ (`MS_wA_reach_SnPres`).
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
- **Log:** a fresh-clone run is saved in `logs/build_axioms_v1.1.log`. It ran on commit 0a76431; the submitted commit differs only in documentation.

## Contribution and prior work (honest scope)

- **Implied by prior work.** R. Sneiderman, *Explicit Andrews–Curtis constructions for square presentations* (github.com/Robby955/ac-square-divisibility, public since 2026-09-12), uses the same official `AC.lean`.
  - He proves `a_period`, `b_period`, `residue_solvable_iff`, `zero_a_solvable`, `zero_b_solvable`, `uniform_family`, `YInversion.solution` and `all_parameters_two`.
  - With our bridge (item 6), these imply the AC-triviality content of items 2 and 3, and of item 1 at the level of triviality.
  - This combination is a paper argument across two repositories; it was not compiled as one Lean project.
  - Our proofs were developed independently, but we claim **no priority** for these statements.
  - The instances $m=\pm1,\pm5$ at $n=2$ are due to Myasnikov (1999) and Havas–Ramsay (2003).
- **Known facts, independently formalized.**
  - The AK(3) link: Shehper et al. (arXiv:2408.15332v2, §3) state that MS(3, ·) presentations of this form are AC-equivalent to AK(3). Carreras (arXiv:2607.23611, Thm 4) certifies this with an explicit path. Fagan et al. (arXiv:2606.21611, App. F) place it in AK(3)'s class.
  - The re-formalized results in item 7. George and Zhao report an earlier Lean formalization of the Shehper et al. results, in their own framework (not the official `AC.lean`). Their repository is announced but not released.
  - The techniques are standard: automorphism invariance and conjugacy modulo a relator (Panteleev–Ushakov, Lemma 3.1, Thm 2.3).
- **Possibly new (not found in the sources we checked; novelty not confirmed):**
  - the AC-equivalence-of-presentations form of the period (Sneiderman's stated a-period passes through a triviality transfer);
  - certified classes $m\equiv2,10 \pmod{12}$ at $n=3$ and $m\equiv2,6,14,18 \pmod{20}$ at $n=4$, which his stated theorems do not cover;
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

Andrews–Curtis (1965); Akbulut–Kirby (1985); Miller–Schupp (1999); Myasnikov (1999); Myasnikov–Myasnikov–Shpilrain (2002, arXiv:math/0302080); Havas–Ramsay (2003); Panteleev–Ushakov (arXiv:1609.00325); Shehper et al. (arXiv:2408.15332v2); Lisitsa, J. Comput. Algebra 16 (2025) 100041; Fagan et al. (arXiv:2606.21611); Carreras (arXiv:2607.23611); R.J. George, "Formalizing the Andrews–Curtis conjecture" (blog, 2026); R. Sneiderman, github.com/Robby955/ac-square-divisibility. Detailed record: `NOVELTY.md`, `research/lit/`.

## GitHub (optional)
- Repository link: https://github.com/suii00/sair-acc-proof
- Commit SHA (40 chars): 4a5644e73f945b7a14ea85d9660a6240baec4ac6

> ⚠ The repo is currently **PRIVATE**. The form requires a public repo for this field. Either:
> - make it public (the user's decision; not done here), and then use the SHA above; or
> - leave this field empty.
>
> If the repo goes public, `research/lit/sources/` is gitignored, so no third-party full texts are committed. Note that
> `report.html` does contain short quoted excerpts.

## arXiv / Paper link (optional)
(leave empty — no paper posted)

## References — "Select one published ACC result that this submission builds on"
Recommendation:
- If R. Sneiderman's submission ("Explicit Andrews–Curtis Constructions for Square Presentations",
  github.com/Robby955/ac-square-divisibility) appears in the selectable list, select it. It is the result whose theorems
  imply much of ours, and the Description compares with it explicitly.
- Otherwise choose the entry for Shehper et al., "What makes math problems hard for reinforcement learning: a case
  study" (arXiv:2408.15332), if listed.
- ⚠ We have not seen the selectable list; verify it in the form.

All other referenced work is described in the Description's "Contribution and prior work" and "References" sections.
