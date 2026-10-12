# Round 6 status (2026-10-13 JST)

## Proven in Lean (compiled, warningAsError, no sorry; #print axioms = [propext, Classical.choice, Quot.sound])
- Period.lean: `MS_wA_period` (MS(n,wA m) ~ MS(n,wA(m+n(n+1)))), `MS_wA_period_mul`, `MS_wA_of_residues` (n>0).
- N3.lean: `MS_wA_mult_succ` (∀n q, m=q(n+1) trivial), `MS_wA_one` (m=1, via w⋆),
  `MS3_wA_m10/m2/m1` (certified search paths, 52/21/45 moves), and
  **`MS3_wA`: ∀m, m mod 12 ∉ {5,7} → MS(3, wA m) AC-trivial.**
- Full `lake build AC ACProof` succeeded; Check.lean prints axioms; grep finds no sorry/admit. Official AC.lean unmodified.

## Not proven
- n=3 residues 5, 7 (mod 12): open (greedy search 4M nodes, no path).
- n=4: Lean covers residues {0,1,4,5,8,10,12,15,16} mod 20 via general lemmas. Search paths for 2,6,14,18,19 exist but
  are NOT certified in Lean this round. Open: 3,7,9,11,13,17.
- n≥5 general: only nℤ ∪ (n+1)ℤ ∪ {1, ±(n+1)} + period.
- The shift-by-(n+1) idea yields exactly the period n(n+1) theorem; it does not alone give all m for n≥3.

## Writeup
draft_writeup.md: added C.7–9, C' (n=4 search status), C'' (paper re-derivation of n=2 all-m via period 6 + residues,
including the 19-move base path in hand-checkable form), updated D.
