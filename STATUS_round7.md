# Round 7 status (2026-10-13 JST)

## Proven in Lean (full `lake build AC ACProof` OK, warningAsError, no sorry/admit,
## #print axioms = [propext, Classical.choice, Quot.sound]; official AC.lean unmodified)
- N4.lean: certified search paths MS4_wA_m2 / _m6 / _m14 (m=-6) / _m18 (m=-2) / _m19 (m=-1), each move an official
  Step (each step a separate theorem to stay within heartbeats); **MS4_wA: m mod 20 ∉ {3,7,9,11,13,17} ⇒ trivial.**
- Symmetry.lean: **MS_wA_negate** (ψ: y ↦ y⁻¹ shows m and −m equivalent), MS_wA_neg_one (∀n, wA(−1)),
  MS_wA_pm_one (∀n, m ≡ ±1 mod n(n+1)).

## Not proven / open
- n=3: class {5,7} mod 12 (now a single class by symmetry).
- n=4: classes {3,17}, {7,13}, {9,11} mod 20.
- Searches (all failed): cyclic-canonical best-first (search2/cyc.py, cycw.py) up to 10M states, supermove variant
  (cyc2.py) 8M states, n=4 6M states. BS(3,4) conjugacy-link search (search2/bs.py): no new links.
- Bidirectional search was NOT implemented (no explicit target set besides the trivial pair; left as future work).

## Files
lean: N4.lean, Symmetry.lean, Check.lean updated. search2/: cyc.py, cycw.py, cyc2.py, bs.py, outputs *.out.
search/: emitn2.py, n4m*.lean.
