#!/usr/bin/env bash
# Reproduce the ACProof build from scratch against the OFFICIAL statement repository.
#   usage: scripts/reproduce.sh [WORKDIR]      (default: a fresh mktemp -d)
# Requirements: git, curl, elan (https://github.com/leanprover/elan) on PATH. Network access.
# What it does:
#   1. clones SAIRcompetition/Andrews-Curtis at the pinned commit;
#   2. checks that AC.lean is byte-identical to the pinned version (sha256);
#   3. copies lean/ACProof/ next to AC.lean and appends ONE [[lean_lib]] entry to lakefile.toml
#      (AC.lean itself is never modified; warningAsError = true comes from the official lakefile);
#   4. fetches the Mathlib cache, builds AC and ACProof, and prints `#print axioms` for every submission theorem;
#   5. fails if any `sorry`/`admit` occurs or any theorem uses an axiom beyond propext/Classical.choice/Quot.sound.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OFFICIAL_URL="https://github.com/SAIRcompetition/Andrews-Curtis.git"
OFFICIAL_COMMIT="a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e"
AC_SHA256="927ba318d26b06c312140117b2a4856373832ed2c043944f520ec7337bcfca1b"
WORK="${1:-$(mktemp -d)}"
echo "== workdir: $WORK"; echo "== research repo: $(git -C "$REPO_ROOT" rev-parse HEAD 2>/dev/null || echo unknown)"
git clone --quiet --filter=blob:none "$OFFICIAL_URL" "$WORK/Andrews-Curtis"
git -C "$WORK/Andrews-Curtis" checkout --quiet "$OFFICIAL_COMMIT"
echo "== official commit: $(git -C "$WORK/Andrews-Curtis" rev-parse HEAD)"
cd "$WORK/Andrews-Curtis/competition/tools/lean"
echo "$AC_SHA256  AC.lean" | sha256sum -c -
grep -q '^warningAsError = true' lakefile.toml && echo "== official lakefile has warningAsError = true"
cp -r "$REPO_ROOT/lean/ACProof" ./ACProof
printf '\n[[lean_lib]]\nname = "ACProof"\nglobs = ["ACProof.+"]\n' >> lakefile.toml
echo "== diff vs official (tracked files):"; git diff --stat
echo "== toolchain: $(cat lean-toolchain)"
lake --version
lake exe cache get
lake build AC ACProof
echo "== sorry/admit scan:"
if grep -rnwE 'sorry|admit' ACProof/*.lean; then echo "FOUND sorry/admit"; exit 1; else echo "none"; fi
echo "== #print axioms (ACProof/Check.lean):"
lake env lean ACProof/Check.lean | tee axioms.out
N=$(grep -c 'depends on axioms' axioms.out); BAD=$(grep 'depends on axioms' axioms.out | grep -vc '\[propext, Classical.choice, Quot.sound\]' || true)
echo "== theorems audited: $N; with nonstandard axioms: $BAD"
[ "$N" -eq "$(grep -c '^#print axioms' ACProof/Check.lean)" ] && [ "$BAD" -eq 0 ] && echo "== REPRODUCE OK"
