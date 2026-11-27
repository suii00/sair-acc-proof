import ACProof.AKThreeConjugations

/-! # The exact conjugation cost of the ordered AK(2) presentation -/

namespace AC

/-- A chronological list of fifteen ordinary moves. The conjugating words are
`xYX`, `xyXX`, and `xY`, with capital letters denoting inverse generators. -/
def AK2ThreeConjugations : List (PrimitiveMove 2) :=
  [.inv 0, .mulRight 1 0 (by decide), .conj 1 (gx * gy⁻¹ * gx⁻¹),
   .mulRight 0 1 (by decide), .inv 1, .conj 1 (gx * gy * gx⁻¹ * gx⁻¹),
   .mulRight 1 0 (by decide), .conj 0 (gx * gy⁻¹), .inv 1,
   .mulRight 0 1 (by decide), .mulRight 1 0 (by decide), .mulRight 0 1 (by decide),
   .mulRight 0 1 (by decide), .inv 1, .mulRight 1 0 (by decide)]

theorem AK2_threeConjugations_witness :
    runMoves (AK 2) AK2ThreeConjugations = standard 2 ∧
    conjCount AK2ThreeConjugations = 3 ∧ AK2ThreeConjugations.length = 15 := by
  refine ⟨?_, rfl, rfl⟩
  apply fin2_ext <;>
    simp [AK2ThreeConjugations, runMoves, PrimitiveMove.apply, AK, standard, gx, gy] <;> group

/-- A shorter path using longer conjugating words `xYX`, `yyXyyXX`, `xYxYY`. -/
def AK2ShortThreeConjugations : List (PrimitiveMove 2) :=
  [.inv 0, .mulRight 1 0 (by decide), .conj 1 (gx * gy⁻¹ * gx⁻¹),
   .mulRight 0 1 (by decide), .conj 1 (gy ^ 2 * gx⁻¹ * gy ^ 2 * gx⁻¹ ^ 2),
   .mulRight 1 0 (by decide), .conj 1 (gx * gy⁻¹ * gx * gy⁻¹ ^ 2), .inv 0,
   .mulRight 1 0 (by decide), .mulRight 0 1 (by decide), .mulRight 0 1 (by decide),
   .mulRight 1 0 (by decide), .mulRight 0 1 (by decide)]

theorem AK2_threeConjugations_short_witness :
    runMoves (AK 2) AK2ShortThreeConjugations = standard 2 ∧
    conjCount AK2ShortThreeConjugations = 3 ∧ AK2ShortThreeConjugations.length = 13 := by
  refine ⟨?_, rfl, rfl⟩
  apply fin2_ext <;>
    simp [AK2ShortThreeConjugations, runMoves, PrimitiveMove.apply, AK, standard, gx, gy] <;> group

/-- Exactly three arbitrary-word conjugations are necessary and sufficient,
with no limit on the number of inversions or right multiplications. -/
theorem AK2_conjCount_exact :
    (∃ ms : List (PrimitiveMove 2), runMoves (AK 2) ms = standard 2 ∧ conjCount ms = 3) ∧
    (∀ ms : List (PrimitiveMove 2), runMoves (AK 2) ms = standard 2 → 3 ≤ conjCount ms) :=
  ⟨⟨AK2ThreeConjugations, AK2_threeConjugations_witness.1, AK2_threeConjugations_witness.2.1⟩,
    AK_three_conjugations (n := 2) (by decide)⟩

end AC
