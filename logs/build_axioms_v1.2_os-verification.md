# v1.2 verification record — Open Math OS reproduce.sh run

- Date: 2026-11-18, 22:07–22:21 JST (browser task window; the reproduce job
  itself reported a duration of 3m09s, OS job id jmwm54bfe).
- Environment: Open Math OS (os.openmathmodel.org), project sair-acc-proof,
  scratch copy of this repo. Nothing was committed or pushed from the OS.
- Flow: scripts/reproduce.sh itself (not an equivalent substitute):
  clone SAIRcompetition/Andrews-Curtis at commit
  a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e, AC.lean sha256 verified OK,
  overlay lean/ACProof/ (with the new N5.lean and updated Check.lean),
  lake exe cache get, lake build AC ACProof, sorry/admit scan,
  Check.lean #print axioms audit.
- Result: exit status 0. Build completed successfully (8270 jobs).

Final audit lines (verbatim from the OS agent's report):

    'AC.MS5_wA_m2' depends on axioms: [propext, Classical.choice, Quot.sound]
    'AC.MS5_wA_m3' depends on axioms: [propext, Classical.choice, Quot.sound]
    'AC.MS5_wA_m27' depends on axioms: [propext, Classical.choice, Quot.sound]
    'AC.MS5_wA_m28' depends on axioms: [propext, Classical.choice, Quot.sound]
    'AC.MS5_wA_m9' depends on axioms: [propext, Classical.choice, Quot.sound]
    'AC.MS5_wA_m21' depends on axioms: [propext, Classical.choice, Quot.sound]
    'AC.MS5_wA' depends on axioms: [propext, Classical.choice, Quot.sound]
    == theorems audited: 66; with nonstandard axioms: 0
    == REPRODUCE OK

- Full OS-side log: .nucleus/jobs/jmwm54bfe.log (inside the OS environment).
- Note: three earlier local reproduce.sh attempts on Muse's VM (2026-11-18)
  failed at the dependency download stage (ProofWidgets release fetch;
  Mathlib git clone, git exit 128) before any compilation began; the failed
  logs are kept locally as build_axioms_v1.2_attempt1-failed.log,
  build_axioms_v1.2.log (attempt 2) and build_axioms_v1.2_attempt3.log.
