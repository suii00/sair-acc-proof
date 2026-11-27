import ACProof.ConjugationTrace
import ACProof.MillerSchupp

/-! An ordinary two-multiplication trivialization for the first metabelian-law pair. -/

namespace AC.MetabelianProbe

private def c : Word 2 := gx * gy * gx⁻¹ * gy⁻¹
private def d : Word 2 := gx⁻¹ * c * gx
private def p : Word 2 := gy * gx
private def q : Word 2 := gy * gx⁻¹ * gy⁻¹ * gx

def law : Word 2 := c * d * c⁻¹ * d⁻¹

def firstPair : Relators 2 := ![gx, gy * law]

def firstMoves : List (PrimitiveMove 2) :=
  [.conj 0 q, .mulRight 1 0 (by decide), .inv 0, .conj 0 (q * gy * q⁻¹),
   .mulRight 1 0 (by decide), .conj 0 (q * gy)⁻¹, .inv 0, .conj 1 p⁻¹]

/-- The chronological path uses two positive right multiplications. -/
theorem first_witness :
    runMoves firstPair firstMoves = standard 2 ∧ mulCount firstMoves = 2 := by
  refine ⟨?_, rfl⟩
  apply fin2_ext <;>
    simp [firstMoves, firstPair, runMoves, PrimitiveMove.apply, law, c, d, p, q,
      standard, gx, gy] <;> group

#print axioms first_witness
end AC.MetabelianProbe
