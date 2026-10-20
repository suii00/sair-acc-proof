# sair-acc-proof — SAIR Andrews–Curtis Challenge, Proof Track (research repo, private)

Lean 4 formalization of AC-triviality results for Miller–Schupp presentations MS(n, y^{-m} x y^m x^{-1}),
checked against the **unmodified** official statement `AC.lean` of
[SAIRcompetition/Andrews-Curtis](https://github.com/SAIRcompetition/Andrews-Curtis) @ `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e`.
The manuscript is in `draft_writeup.md`. It contains the main theorems, paper proofs, a theorem ↔ Lean table, the classification
(known / corollary / under novelty investigation / unproven), and sources.

## Main results (submission candidate v1.1) and prior-art status
**Read NOVELTY.md §v1.1 first.** R. Sneiderman's public Lean repo (github.com/Robby955/ac-square-divisibility, 2026-09-12,
same official AC.lean) proves results that imply the AC-triviality content of our period, `MS_wA_cover` and n = 2
theorems. Our `MS_wA_reach_SnPres` (Comparison.lean) gives the correspondence.
- **Period (all n):** MS(n, wA m) ~ MS(n, wA(m + t·n(n+1))) (`MS_wA_period_mul`). The triviality consequence is implied by
  [Sn]. Our statement is the AC-equivalence-of-presentations form.
- **n = 2, all m ∈ ℤ:** MS(2, wA m) is AC-trivial (`MS2_wA_all'`, `MS2_wA_all`). Implied by [Sn] `all_parameters_two`;
  the m = ±1, ±5 instances are due to Myasnikov / Havas–Ramsay.
- **All n:** AC-trivial for m ∈ nℤ ∪ (n+1)ℤ ∪ (±1 + n(n+1)ℤ) (`MS_wA_cover`). Implied by [Sn].
- **AC-triviality transfer:** `MS_wA_negate` (y ↦ y⁻¹). This is a known principle and NOT an AC path.
- **n = 3:** AC-trivial unless m ≡ ±5 mod 12 (`MS3_wA`). **n = 4:** AC-trivial unless m ≡ ±3, ±7, ±9 mod 20 (`MS4_wA`).
  The cells m ≡ 2, 10 (mod 12) and m ≡ 2, 6, 14, 18 (mod 20) were not found in the sources checked.
- **AK links (independent formal proofs):** MS(3, wA 5) triv ⇔ AK(3) triv (`MS3_wA5_iff_AK3`, known: Shehper v2 §3,
  Carreras Thm 4); MS(4, wA(−9)) triv ⇔ AK(4) triv (`MS4_wAm9_iff_AK4`, novelty unconfirmed).
- No stable-AC statement is used. Lisitsa's stable AK(3) claim was withdrawn in J. Comput. Algebra 16 (2025) 100041.

## Reproducing (clean environment)
Requirements: `git`, `elan` (Lean toolchain manager), network access. From the repo root:
```
scripts/reproduce.sh [WORKDIR]
```
The script clones the official repo at the pinned commit and checks the sha256 of `AC.lean`. It copies `lean/ACProof/` next to
`AC.lean` and appends a single `[[lean_lib]] ACProof` entry to `lakefile.toml`; nothing else in the official repo changes. The
official lakefile already sets `warningAsError = true`. It then runs `lake exe cache get` and `lake build AC ACProof`, scans for
`sorry`/`admit`, and runs `#print axioms` on all theorems listed in `lean/ACProof/Check.lean`. It ends with `REPRODUCE OK`
only if every theorem depends on a subset of `{propext, Classical.choice, Quot.sound}`.
Logs of runs from a fresh clone: `logs/build_axioms_v1.log` (v1, 48 theorems) and `logs/build_axioms_v1.1.log`
(v1.1, 59 theorems: 57 use exactly the three axioms, `bs_pow` uses [propext], `link_identity` uses [propext, Quot.sound]).

## Layout
- `lean/ACProof/` — Lean sources. Dependency order: Consequence → MillerSchupp, Basic → MS1 → MSwk → MS2 → AK → NewFamilies
  → Period → (Tactics) → General → {MS2Alt, N3, N4}; N3 → AK3Link → AK4Link (also imports N4); NewFamilies → Comparison;
  MS2All imports NewFamilies only. General lemmas never import instance files. `Check.lean` imports everything.
- `scripts/reproduce.sh`, `logs/` — reproducibility.
- `NOVELTY.md`, `research/lit/` — prior-art record (imozuru method: map.md, log.md, extracts.json, report.html; the
  source copies in `research/lit/sources/` are gitignored). `research/n3-m5/` — n = 3/4 research log (merged from the
  branch).
- `search/`, `search2/` — search and emission scripts and raw outputs (experiments, not results).
- `literature.md`, `themes.md`, `STATUS_round*.md` — research records (historical; rounds 6–7 use "~" loosely for
  "AC-triviality equivalent"; the manuscript and this README are authoritative).

## License
Licensed under the [Apache License 2.0](LICENSE), the same license as the official
[SAIRcompetition/Andrews-Curtis](https://github.com/SAIRcompetition/Andrews-Curtis) repository. The official `AC.lean` is
not included here; `scripts/reproduce.sh` fetches it from the pinned upstream commit.
