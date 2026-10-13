# sair-acc-proof — SAIR Andrews–Curtis Challenge, Proof Track (research repo, private)

Lean 4 formalization of AC-triviality results for Miller–Schupp presentations MS(n, y^{-m} x y^m x^{-1}),
checked against the **unmodified** official statement `AC.lean` of
[SAIRcompetition/Andrews-Curtis](https://github.com/SAIRcompetition/Andrews-Curtis) @ `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e`.
The manuscript is in `draft_writeup.md`. It contains the main theorems, paper proofs, a theorem ↔ Lean table, the classification
(known / corollary / under novelty investigation / unproven), and sources.

## Main results (submission candidate v1)
- **Period (all n):** MS(n, wA m) and MS(n, wA(m + t·n(n+1))) are AC-equivalent presentations (`MS_wA_period_mul`).
- **n = 2, all m ∈ ℤ:** MS(2, wA m) is AC-trivial. `MS2_wA_all'` proves it as a corollary of the general families, with no
  search path; `MS2_wA_all` is the alternative proof via a certified 19-move path.
- **All n:** AC-trivial for m ∈ nℤ ∪ (n+1)ℤ ∪ (±1 + n(n+1)ℤ) (`MS_wA_cover`).
- **AC-triviality transfer (all n):** if MS(n, wA(−m)) is AC-trivial, so is MS(n, wA m) (`MS_wA_negate`). This is NOT a
  constructed AC path between the two presentations.
- **n = 3:** AC-trivial unless m ≡ ±5 mod 12 (`MS3_wA`). **n = 4:** AC-trivial unless m ≡ ±3, ±7, ±9 mod 20 (`MS4_wA`).
  The listed classes are open.

## Reproducing (clean environment)
Requirements: `git`, `elan` (Lean toolchain manager), network access. From the repo root:
```
scripts/reproduce.sh [WORKDIR]
```
The script clones the official repo at the pinned commit and checks the sha256 of `AC.lean`. It copies `lean/ACProof/` next to
`AC.lean` and appends a single `[[lean_lib]] ACProof` entry to `lakefile.toml`; nothing else in the official repo changes. The
official lakefile already sets `warningAsError = true`. It then runs `lake exe cache get` and `lake build AC ACProof`, scans for
`sorry`/`admit`, and runs `#print axioms` on all theorems listed in `lean/ACProof/Check.lean`. It ends with `REPRODUCE OK`
only if every theorem depends on exactly `[propext, Classical.choice, Quot.sound]`.
The log of a run from a fresh clone is in `logs/build_axioms_v1.log`.

## Layout
- `lean/ACProof/` — Lean sources. Dependency order: Consequence → MillerSchupp, Basic → MS1 → MSwk → MS2 → AK → NewFamilies
  → Period → (Tactics) → General → {MS2Alt, N3, N4}; MS2All imports NewFamilies only. General lemmas never import instance files.
- `scripts/reproduce.sh`, `logs/` — reproducibility.
- `search/`, `search2/` — search and emission scripts and raw outputs (experiments, not results).
- `literature.md`, `themes.md`, `STATUS_round*.md` — research records (historical; rounds 6–7 use "~" loosely for
  "AC-triviality equivalent"; the manuscript and this README are authoritative).
