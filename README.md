# sair-acc-proof — SAIR Andrews–Curtis Challenge, Proof Track (research repo)

Lean 4 formalization of AC-triviality results for Miller–Schupp presentations MS(n, y^{-m} x y^m x^{-1}),
checked against the **unmodified** official statement `AC.lean` of
[SAIRcompetition/Andrews-Curtis](https://github.com/SAIRcompetition/Andrews-Curtis) @ `a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e`.

## v1.3 submission candidate

For every $n\in\mathbb N$ and $t\in\mathbb Z$, the ordered presentation $\mathrm{MS}(n,w_A(m))$ reaches $\mathrm{AK}(n)$ by ordinary Andrews–Curtis moves when $m=-(2n+1)+tn(n+1)$. For $m=\pm(2n+1)+tn(n+1)$, the two presentations have equivalent AC-triviality. For $n>0$ these are residue classes modulo $n(n+1)$. In the classical range $n\ge2$ the proof identifies an explicit parameter in the theorems of Sneiderman, Shehper et al., and Myasnikov–Myasnikov–Shpilrain. [Lean proof](lean/ACProof/AKFamily.lean) · [Manuscript](draft_writeup.md)

At $n=5$ the conclusions depend on the residue of $m$ modulo 30.

| Residues | Result | Evidence |
|---|---|---|
| 0, 1, 5, 6, 10, 12, 15, 18, 20, 24, 25, 29 | AC-trivial | General families in `MS_wA_cover` |
| 2, 3, 9, 21, 27, 28 | AC-trivial | Six Lean path certificates for short representatives already covered by Fagan et al. |
| 11, 19 | AC-trivial iff AK(5) is | `MS5_wA_11_19_iff_AK5` for both classes and an ordinary path to AK(5) throughout class 19 |
| 4, 26 | AC-trivial by published benchmark results and reduction | Literature comparison only |
| 7, 8, 13, 14, 16, 17, 22, 23 | AC-triviality undecided here | — |

`MS5_wA` certifies the first two rows, **18 of the 30 classes**, for every integer in those classes. The earlier submission, ACC-P000018, contains the period, the complete $n=2$ result, partial $n=3,4$ results and two specialized AK transfers. The v1.3 manuscript gives the theorem-to-code correspondence and the benchmark matches. [Earlier SAIR entry](https://competition.sair.foundation/contributor-network/acc/ACC-P000018) · [Prior-art record](NOVELTY.md) · [Fagan et al., Table 2](https://arxiv.org/html/2606.21611v1#A6.T2)

## Reproduction

With Git, elan and network access, run this command from the repository root.

```sh
scripts/reproduce.sh
```

The script fetches the pinned official Lean project, verifies the SHA-256 of `AC.lean`, overlays `lean/ACProof/`, and runs the build with warnings treated as errors. Its axiom audit checks every declaration named in `Check.lean` against `propext`, `Classical.choice`, and `Quot.sound`. It prints `REPRODUCE OK` on success. [Reproduction script](scripts/reproduce.sh) · [Audit declarations](lean/ACProof/Check.lean)

On 27 November 2026 (JST), Open Math OS ran the script from a clean checkout of proof commit `f2ba667089229bcc4a1c0c0576c407c9ac3794c9` with Lean 4.29.1 and Mathlib `5e932f97`. All 71 audited theorems passed. The five AK family declarations each depend on `propext`, `Classical.choice` and `Quot.sound`. The run exited with code 0. An independent macOS build of the same commit produced the same 71 audit results. [Open Math OS full build log](logs/build_axioms_v1.3.log) · [Audited proof commit](https://github.com/suii00/sair-acc-proof/commit/f2ba667089229bcc4a1c0c0576c407c9ac3794c9)

The v1.2 Open Math OS verification recorded 66 declarations. Earlier raw logs cover v1.1 and its documentation-only update. [v1.2 verification record](logs/build_axioms_v1.2_os-verification.md) · [v1.1 raw log](logs/build_axioms_v1.1_3ff15e7.log)

## Repository guide

- `lean/ACProof/` contains the proofs. `Period.lean` supplies paths between periodic translates, `N5.lean` contains the six search certificates, and `AKFamily.lean` proves the uniform AK result.
- `submission/` holds the Proof Track form and descriptions. `draft_writeup.md` contains the paper proofs and references.
- `search/` and `search2/` contain exploratory programs and output. `research/` and the dated `STATUS_round*.md` files preserve prior-art and search history.

## License
Licensed under the [Apache License 2.0](LICENSE), the same license as the official
[SAIRcompetition/Andrews-Curtis](https://github.com/SAIRcompetition/Andrews-Curtis) repository. The official `AC.lean` is
not included here; `scripts/reproduce.sh` fetches it from the pinned upstream commit.
