import ACProof.AK
import ACProof.ConjugationTrace

/-! # An AK(1) trivialization with two conjugations -/

namespace AC

/-- Invert the first relator to get `y²x⁻¹`. Two right products and two
conjugations turn the second relator into `y³x⁻¹`. After inverting the first
relator again, three right products give `(x,y)`. -/
def AK1TwoConjugations : List (PrimitiveMove 2) :=
  [.inv 0, .mulRight 1 0 (by decide), .conj 1 (gy⁻¹ * gx⁻¹),
   .mulRight 1 0 (by decide), .conj 1 (gx * gy * gx⁻¹),
   .inv 0, .mulRight 1 0 (by decide),
   .mulRight 0 1 (by decide), .mulRight 0 1 (by decide)]

/-- A word-level certificate in the three official operations, in chronological order. -/
theorem AK1_twoConjugations_witness :
    runMoves (AK 1) AK1TwoConjugations = standard 2 ∧
    conjCount AK1TwoConjugations = 2 ∧ AK1TwoConjugations.length = 9 := by
  refine ⟨?_, rfl, rfl⟩
  apply fin2_ext <;>
    simp [AK1TwoConjugations, runMoves, PrimitiveMove.apply, AK, standard, gx, gy] <;> group

end AC
