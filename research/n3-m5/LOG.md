# research/n3-m5 — target: `Reachable (MS 3 (wA 5)) (standard 2)`
Rules: each hypothesis records its method and its success/failure conditions. **Verified** = Lean-checked, axioms audited.
**Experiment** = computation only. A failed search is never evidence of non-triviality. Stable AC goes in its own section.

Known reductions (verified, main): by period + transfer, MS(3, wA m) for m ≡ 5 or 7 mod 12 are all AC-triviality
equivalent to MS(3, wA 5).

## H1 — automorphisms fixing r0 up to conjugacy (parameter transformation) — EXPERIMENT → used in H5
Observation (paper, then Lean in H5): φ_{j,k}: x ↦ yʲ x yᵏ, y ↦ y sends r0 = x⁻¹y³xy⁻⁴ to a conjugate of r0. It sends
r1 = x·wA(m)⁻¹ to a conjugate of x y^{j+k} x y^{-m} x⁻¹ y^m. Every presentation (r0, x yˢ x y⁻⁵ x⁻¹ y⁵), s ∈ ℤ, is therefore
AC-triviality-equivalent to MS(3, wA 5) (transfer through an automorphism and its inverse).
Experiment (scripts/h2.py): cyclic search at 400k states for s ∈ [−6,6]\{0}: none solved. Success condition: any s solved.
Result: FAILED (no evidence either way).

## H2 — landscape of (r0, x yᵃ x yᵇ x⁻¹ yᶜ), |b|,|c| ≤ 6, |a| ≤ 2 — EXPERIMENT
scripts/h3scan.py at 20k states per instance: 554/845 solved. Every (b,c) with no solved a has odd b (list in h3scan.out).
H2-link (scripts/h3link.py): no BS(3,4)-conjugacy (conjugators of length ≤ 4) from x yᵃ x y⁻⁵ x⁻¹ y⁵ (|a| ≤ 4) to any
solved instance. Success condition: a link plus a solved target. Result: FAILED.

## H3 — link to the w_k / AK(3) family — SUCCESS (VERIFIED in Lean)
Hypothesis: r1 for wA 5, after an automorphism φ, is BS(3,4)-conjugate to x·w_k⁻¹ for some k.
Method: scripts/h5.py checks conjugacy with Britton reduction. Hits include a = 3, k = 8 with conjugator x⁻¹. The affine
representation y: t ↦ t+1, x: t ↦ (3/4)t also sends the relation to the identity (sanity check, not a proof).
Paper proof: in BS(3,4), y³x = xy⁴ and y⁶x = xy⁸, so
  x⁻¹·(x y³ x y⁻⁵ x⁻¹ y⁵)·x = y³ x y⁻⁵ x⁻¹ y⁵ x = x y⁻¹ x⁻¹ y⁵ x = x y⁻¹ x⁻¹ y⁻¹ (y⁶ x) = x y⁻¹ x⁻¹ y⁻¹ x y⁸ = x·w₈⁻¹.
Hence φ := (x ↦ x y³) maps MS(3, wA 5) to a presentation AC-equivalent to MS(3, w₈), and MS(3, w₈) ~ MS(3, w₁) ~ AK(3)
([SMF] Thm 6, [MMS] Prop 1.3).
**Verified (lean/ACProof/AK3Link.lean; axioms standard):**
- `phi_MS3_wA5_reach_wk8`: Reachable (phiK 3 ∘ MS 3 (wA 5)) (MS 3 (wk 8)) — a genuine AC path.
- **`MS3_wA5_iff_AK3`: Reachable (MS 3 (wA 5)) (standard 2) ↔ Reachable (AK 3) (standard 2)**. This is a two-way transfer of
  AC-triviality through the automorphism φ and its inverse. No AC path between MS(3, wA 5) and AK(3) is constructed.
- `MS3_wA_of_AK3`: if AK(3) is AC-trivial, then MS(3, wA m) is AC-trivial for EVERY m ∈ ℤ.
Consequence: the target is exactly as hard as the AK(3) problem, which is open (Shehper et al. v2 list AK(3) as open).
More search budget is therefore very unlikely to help, and a proof of the target would settle AK(3).
Novelty: NOT checked yet. Any known AC-equivalence between AK(3) and MS(3, w) for other w should be compared.

## Stable AC (separate; NOT pursued)
MMS02 Prop 1.2 states AK(3) is stably AC-trivial. Shehper et al. v2 report a misprint in MMS02 and retract their own v1 claim
about AK(3). The status needs a careful reading before any use. If a correct stable trivialization of AK(3) exists, the same
automorphism transfer should give a stable trivialization of MS(3, wA 5), since the official `StableStep` setting is also
preserved by endomorphisms. This would need a separate formalization (official `AC.StableStep`); it has not been attempted.

## H4 — does the H3 mechanism extend to n = 4 (link with AK(4))? — EXPERIMENT only
scripts/h5n.py (Britton conjugacy, conjugators of length ≤ 6, |a| ≤ 6, |k| ≤ 14):
- n = 4, m = −9 (class {9, 11} mod 20): HIT a = −6, k = −9, conjugator y⁻¹x⁻¹y⁻⁴. This suggests MS(4, wA(−9)) is
  AC-triviality-equivalent to AK(4). NOT verified: no hand derivation or Lean proof yet.
- n = 4, m ∈ {3, 7, −3, −7}: no hit within these bounds (classes {3,17}, {7,13}).
- n = 3, m ∈ {−5, 7, 2, 10}: no hit within these bounds. The m = 5 hit is enough for the whole class via period and transfer.
Next step: derive the BS(4,5) identity for the n = 4 hit and formalize it the same way as AK3Link.
