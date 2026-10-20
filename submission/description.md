Conjecture: AC. Direction: proof (partial result). No claim is made about the full conjecture.

# Miller–Schupp presentations MS(n, y^{-m} x y^m x^{-1}): Lean formalization against the official AC.lean, with prior-art accounting

## What is established
All theorems below are kernel-checked in Lean 4 (v4.29.1, Mathlib 5e932f97) against the UNMODIFIED official AC.lean of
SAIRcompetition/Andrews-Curtis @ a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e (`AC.Reachable`, `AC.standard`).
- No `sorry`, `admit` or `native_decide`; the build uses warningAsError.
- `#print axioms` over all 59 audited theorems gives only axioms from {propext, Classical.choice, Quot.sound}.
- `scripts/reproduce.sh` clones the official repo at the pinned commit, checks the sha256 of AC.lean, builds, and audits
  axioms. Logs of runs from a fresh clone: `logs/build_axioms_v1.1.log`
  and the rerun `logs/build_axioms_v1.1_3ff15e7.log` (2026-10-21).

Notation: MS(n, w) = ⟨x, y | x⁻¹yⁿx = y^{n+1}, x = w⟩ (Miller–Schupp), wA(m) = y^{-m} x y^m x⁻¹,
AK(n) = ⟨x, y | xⁿ = y^{n+1}, xyx = yxy⟩. "AC-trivial" means `Reachable R (standard 2)`; "R ~ S" means `Reachable R S`.

Main results (Lean names in parentheses), each with its prior-art status:
1. Correspondence (`MS_wA_reach_SnPres`): MS(n, wA m) ~ Sneiderman's three-parameter presentation at (a, b, c) = (−m, m, 0).
   This is how we compare our results with his (see "Work by others").
2. Period, all n (`MS_wA_period_mul`): MS(n, wA m) ~ MS(n, wA(m + t·n(n+1))) for all t ∈ ℤ. The triviality consequence
   follows from Sneiderman's `residue_solvable_iff`. Our statement is the AC-equivalence-of-presentations form, a minor
   refinement.
3. n = 2, all m ∈ ℤ (`MS2_wA_all'`): MS(2, wA m) is AC-trivial. This follows from Sneiderman's `all_parameters_two`.
   The instances m = ±1, ±5 are due to Myasnikov (1999) and Havas–Ramsay (2003).
4. All n (`MS_wA_cover`): AC-trivial for m ∈ nℤ ∪ (n+1)ℤ ∪ (±1 + n(n+1)ℤ). This follows from Sneiderman's theorems.
5. n = 3 (`MS3_wA`): AC-trivial unless m ≡ ±5 (mod 12). n = 4 (`MS4_wA`): AC-trivial unless m ≡ ±3, ±7, ±9 (mod 20).
   - The cells m ≡ 2, 10 (mod 12) and m ≡ 2, 6, 14, 18 (mod 20) are not covered by Sneiderman's stated theorems, and we
     did not find them in the sources we checked.
   - They rest on explicit move sequences (21 to 132 moves) found by computer search. Each move is one official `Step`.
   - They are finite base cases; benchmark datasets we did not check may contain them.
6. AK links (independent formal proofs):
   - `MS3_wA5_iff_AK3`: MS(3, wA 5) is AC-trivial iff AK(3) is. Hence if AK(3) is AC-trivial, MS(3, wA m) is AC-trivial
     for every m (`MS3_wA_of_AK3`). This is a known fact in a stronger form (Shehper et al.; Carreras).
   - `MS4_wAm9_iff_AK4`: MS(4, wA(−9)) is AC-trivial iff AK(4) is. Hence if AK(4) is AC-trivial, so is MS(4, wA m) for
     every m ≡ ±9 (mod 20) (`MS4_wA_9_11_of_AK4`). We could not confirm whether this is new.
   - Both are transfers of AC-triviality through the automorphism x ↦ xy^k plus one Baumslag–Solitar identity. They are
     not AC paths.
7. Re-formalization of known results against the official definitions: MS(1, w) for all w; MS(n, y⁻¹xyx⁻¹) for all n;
   MS(n, w_k) ~ MS(n, w_{k+1}); MS(2, w_k) for all k; AK(n) ~ MS(n, w_1); MS(n, w_k) ~ P(n, k); AK(2)
   (Shehper et al.; Myasnikov–Myasnikov–Shpilrain). Here w_k = y^{-k}x⁻¹yxy.

What may be new is therefore small: the Lean certificates for the finite cells in item 5, the AK(4) link in item 6, and
the AC-equivalence form of the period.

## What remains open
- n = 3, m ≡ ±5 (mod 12). This class is equivalent in AC-triviality to AK(3).
- n = 4, m ≡ ±3, ±7 (mod 20), and m ≡ ±9 (mod 20), which is equivalent in AC-triviality to AK(4).
- n ≥ 5 outside item 4.
- No stable-AC statement is made or used. The AC conjecture itself is not addressed.
- Our searches failed on the open classes (up to 10M states). This is not evidence that they are non-trivial.

## Work by others: what we use and how
- SAIRcompetition/Andrews-Curtis, `competition/tools/lean/AC.lean` @ a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e
  (https://github.com/SAIRcompetition/Andrews-Curtis). We use the official definitions unchanged.
- Robert Sneiderman, "Explicit Andrews–Curtis Constructions for Square Presentations",
  https://github.com/Robby955/ac-square-divisibility @ b157f43fc0be4c59c3a517ec6464f27eaa72b8a0. The relevant files are
  unchanged since 66514f4efef874280da5df34d6f747b6cf68029a (2026-09-12).
  - He proved period, residue and n ≤ 2 results for a three-parameter Miller–Schupp family against the same AC.lean.
  - With our correspondence lemma (item 1), his theorems imply the AC-triviality content of our items 2–4. We found his
    repository after our proofs were written. Our proofs are independent; we do not import his code.
  - This combination is a paper argument across two repositories, not a joint Lean build.
- A. Shehper, A. Medina-Mardones, L. Fagan, B. Lewandowski, A. Gruen, Y. Qiu, P. Kucharski, Z. Wang, S. Gukov, "What
  makes math problems hard for reinforcement learning: a case study", arXiv:2408.15332 (v2, Feb 2025; NeurIPS 2025).
  - Thms 2, 3, 6, 7, Prop 5 and Cor 9 are the results re-formalized in item 7.
  - §3 states that ⟨x⁻¹y³x = y⁴, x = y⁻¹x²y⁻¹⟩ is AC-equivalent to AK(3). Our MS(3, wA 5) is AC-equivalent to it.
- Josep Carreras, "Machine-checkable equivalence certificates at the length-14 Andrews–Curtis frontier",
  arXiv:2607.23611. Thm 4 certifies MS(3, y⁻¹x²y⁻¹) ~ AK(3) with an explicit move sequence, so our item 6 (AK(3)) is
  known.
- L. Fagan, M. Tarquini, A. Shehper, et al., S. Gukov, "The Two-Hump Problem", arXiv:2606.21611 (ICML 2026). App. F
  classifies the Miller–Schupp benchmark. MS(3, yxyx⁻¹) is in class 13₁ (AK(3)), and MS(4, yxyx⁻¹) is in class 15₁.
- D. Panteleev, A. Ushakov, "Conjugacy search problem and the Andrews–Curtis conjecture", arXiv:1609.00325 (Groups
  Complexity Cryptology, 2019). Lemma 3.1 (automorphisms preserve AC-triviality) and Thm 2.3 (replacing a relator by a
  conjugate modulo the other relator) are the standard techniques behind our transfers and our period proof.
- A.D. Myasnikov, A.G. Myasnikov, V. Shpilrain, "On the Andrews–Curtis equivalence", Contemp. Math. 296 (2002),
  arXiv:math/0302080. Prop 1.1 (AK(2)) and Prop 1.3 (AK(n) ~ MS(n, w_1)) are re-formalized in item 7.
- C.F. Miller III, P.E. Schupp, Contemp. Math. 250 (1999): the definition of MS(n, w). S. Akbulut, R. Kirby, Topology
  24 (1985): the definition of AK(n).
- A.D. Myasnikov, IJAC 9 (1999); G. Havas, C. Ramsay, IJAC 13 (2003) 61–68: earlier trivializations of
  MS(2, y^{±1}xy^{±1}x⁻¹), i.e. our m = ±1, ±5 at n = 2.
- Related, not used: R.J. George (with A. Zhao), "Formalizing the Andrews–Curtis conjecture" (blog, June 2026,
  https://www.robertj1.com/ai4science/ac-conjecture-aristotle/). It reports an earlier formalization of the Shehper et al.
  results in its own framework, not against the official AC.lean. The repository was not yet released when we checked, so
  item 7 is a re-formalization against the official definitions, not a first formalization.

## Use of AI
This work was done with an AI assistant, Claude Code (Anthropic). It was used to write the Lean proofs, run the computer
searches, and search and read the literature. The proved statements rest on the Lean kernel check against the official
definitions, not on the AI. The prior-art statements were checked against the cited sources.

## Where to look
- Manuscript with paper proofs and the theorem ↔ Lean table: `draft_writeup.md`.
- Prior-art record: `NOVELTY.md` and `research/lit/`.
- Lean sources: `lean/ACProof/`; `lean/ACProof/Check.lean` lists every audited theorem.
