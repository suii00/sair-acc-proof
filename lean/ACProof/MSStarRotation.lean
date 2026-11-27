import ACProof.MSStarThree

/-! A two-letter cyclic rotation changes the ordinary conjugation cost of MS(1,wstar). -/

namespace AC

/-- The first relator rotates from XyxYY to xYYXy, where capitals denote inverses.
The second relator keeps its original basepoint. -/
def msStarOneRotated : Relators 2 :=
  ![gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy, (MS 1 wstar) 1]

theorem msStarOne_rotate :
    (PrimitiveMove.conj 0 (gy⁻¹ * gx)).apply (MS 1 wstar) = msStarOneRotated := by
  apply fin2_ext
  · simp [PrimitiveMove.apply, MS, msStarOneRotated]
    group
  · simp [PrimitiveMove.apply, MS, msStarOneRotated]

/-- The nine chronological ordinary moves after rebasing. -/
def msStarOneRotatedMoves : List (PrimitiveMove 2) :=
  [.inv 0, .mulRight 1 0 (by decide), .inv 0,
   .conj 1 (gy⁻¹ * gx⁻¹), .mulRight 0 1 (by decide), .inv 0,
   .conj 1 (gx⁻¹ * gy), .mulRight 1 0 (by decide), .inv 0]

theorem msStarOneRotated_witness :
    runMoves msStarOneRotated msStarOneRotatedMoves = standard 2 ∧
    conjCount msStarOneRotatedMoves = 2 ∧ msStarOneRotatedMoves.length = 9 := by
  refine ⟨?_, rfl, rfl⟩
  apply fin2_ext <;>
    simp [msStarOneRotated, msStarOneRotatedMoves, runMoves, PrimitiveMove.apply,
      MS, wstar, standard, gx, gy] <;> group

/-- The minimum conjugation count is exactly two for the rotated tuple. -/
theorem msStarOneRotated_exact :
    (∀ ms : List (PrimitiveMove 2), runMoves msStarOneRotated ms = standard 2 →
      2 ≤ conjCount ms) ∧
    ∃ ms : List (PrimitiveMove 2), runMoves msStarOneRotated ms = standard 2 ∧
      conjCount ms = 2 := by
  refine ⟨?_, ⟨msStarOneRotatedMoves, msStarOneRotated_witness.1,
    msStarOneRotated_witness.2.1⟩⟩
  intro ms h
  have hfull : runMoves (MS 1 wstar) (.conj 0 (gy⁻¹ * gx) :: ms) = standard 2 := by
    simpa only [runMoves, msStarOne_rotate] using h
  have hcost := MSStarThree.lower hfull
  change 3 ≤ 1 + conjCount ms at hcost
  omega

#print axioms msStarOneRotated_exact
end AC
