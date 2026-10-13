# ACC Proof Track research records (2026-10-13 JST)
- Repo: /workspace/Andrews-Curtis @ a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e (AC.lean untouched)
- Toolchain: elan + Lean 4.29.1, Mathlib 5e932f97 (pinned); `lake build` of AC OK.
- Local addition: `[[lean_lib]] ACProof` appended to lakefile.toml (does not touch AC.lean).
- Lean files: lean/Consequence.lean, lean/MillerSchupp.lean, lean/Check.lean; log lean/build_axioms.log
- literature.md, themes.md
Build (original setup): cd /workspace/Andrews-Curtis/competition/tools/lean && lake build ACProof

## Standalone build
This repo builds on its own; Lake fetches the official `AC.lean` and Mathlib, so neither is vendored.
- `lakefile.toml`: requires `ACStatement` from https://github.com/SAIRcompetition/Andrews-Curtis
  (`competition/tools/lean` @ a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e) and Mathlib 5e932f97 (same as official).
- `lean-toolchain`: Lean 4.29.1. `lake-manifest.json`: pins all transitive dependencies.
- Sources: `ACProof/*.lean` (`lean/` holds the same files plus scripts).

```sh
lake exe cache get   # prebuilt Mathlib
lake build           # builds ACProof (Check.lean prints the axiom report)
```


## Round 6–7 summary (2026-10-13)
- Period theorem (all n): MS(n,wA m) ~ MS(n,wA(m+n(n+1))). Symmetry (all n): m ~ −m.
- All n: wA m trivial for m ∈ nℤ ∪ (n+1)ℤ ∪ (±1 + n(n+1)ℤ). n=2: all m.
- n=3: all m except m ≡ ±5 mod 12 (open). n=4: all m except m ≡ ±3, ±7, ±9 mod 20 (open).
- Lean files: Period.lean, N3.lean, N4.lean, Symmetry.lean (all compiled, axioms checked). See STATUS_round6/7.md.
