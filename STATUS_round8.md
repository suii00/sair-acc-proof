# Round 8 status (2026-11-18 JST) — n = 5 extension (v1.2)

## Proven in Lean (full `lake build AC ACProof` OK, warningAsError, no sorry/admit,
## #print axioms = [propext, Classical.choice, Quot.sound]; official AC.lean unmodified)
- N5.lean (new): certified search paths MS5_wA_m2 (52 moves, w_A(2) itself),
  MS5_wA_m3 (30 moves, reduced representative), MS5_wA_m27 = w_A(−3) (28 moves, representative),
  MS5_wA_m28 = w_A(−2) (54 moves, w_A(−2) itself), MS5_wA_m9 = w_A(−21) (96 moves, representative),
  MS5_wA_m21 = w_A(−9) (44 moves, representative); each step a separate theorem (step_tac3),
  wrappers via MS_wA_reduce, following the N4.lean pattern.
  **MS5_wA: m mod 30 ∉ {4,7,8,11,13,14,16,17,19,22,23,26} ⇒ trivial** (18 of 30 classes).
- Check.lean: import ACProof.N5 added; audit list extended by the 6 base theorems + MS5_wA (66 total).

## Novelty check for the n = 5 cells (2026-11-18)
- Sneiderman's stated theorems cover exactly the complementary 12 classes at n = 5
  (cells a≡0, b≡0, (4,1), (1,5)); the six new cells are (3,2), (2,3), (3,3), (2,4), (1,3), (4,3).
- Mulay's ACC-P000013 (read in full): only the line w = w_A(1), quantitative; no Lean, no
  residue classification. No overlap with the n = 5 classes.
- Benchmark tables (Shehper/Fagan) NOT checked for n = 5 instances: novelty NOT confirmed.

## Not proven / open
- n=5: classes {4,26}, {7,23}, {8,22}, {11,19}, {13,17}, {14,16} mod 30 (negation pairs).
  The {11,19} pair contains cell (1,1) (m ≡ 19) — the AK-linked pattern at n = 3, 4.
  Whether it is equivalent in triviality to AK(5) was NOT checked; no claim is made.

## Searches (experiments, not results)
- search/classes.py at n = 5 (best-first, maxlen 30, up to 8 reduced representatives per class):
  200k-state quick pass solved the pairs m≡±2 (52 moves) and m≡±3 (30 moves) immediately.
  2M-state pass: additionally solved m≡±9 (96 moves, via m=−21) and m≡±21 (44 moves, via m=−9);
  no path found for the pairs {4,26}, {7,23}, {8,22}, {11,19}, {13,17}, {14,16}.
  Failure of the search is not evidence that the presentations are non-trivial.

## Files
lean: N5.lean (new), Check.lean updated. NOVELTY.md, draft_writeup.md updated to v1.2.
search/: classes.py runs logged 2026-11-18; target27.py (targeted driver for residues 27, 28).

## Verification gate (2026-11-18)
- Local reproduce.sh attempts (3 runs on Muse's VM) all failed at the dependency
  download stage (ProofWidgets release fetch; Mathlib git clone) — before any
  compilation. These were network failures, not proof failures.
- Final gate run in Open Math OS (Lean-specialised VM), 2026-11-18 22:07–22:21 JST:
  scripts/reproduce.sh itself, end-to-end, exit status 0 (OS job jmwm54bfe).
  Build completed successfully (8270 jobs); audit: 66 theorems audited,
  0 with nonstandard axioms; final line `== REPRODUCE OK`.
  Record: logs/build_axioms_v1.2_os-verification.md.
