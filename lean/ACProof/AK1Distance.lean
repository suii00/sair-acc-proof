import ACProof.AK1MulLower
import ACProof.AK1MulParity
import ACProof.ConjugationLength

/-! # Exact directed ordinary Andrews–Curtis distance for the ordered AK(1) pair -/

namespace AC

/-- Every ordinary trivialization needs five right products, two conjugations,
and two inversions. The inversion bound subtracts both other operation counts. -/
theorem AK1_min_operation_counts (ms : List (PrimitiveMove 2))
    (h : runMoves (AK 1) ms = standard 2) :
    5 ≤ mulCount ms ∧ 2 ≤ conjCount ms ∧ mulCount ms + conjCount ms + 2 ≤ ms.length := by
  have hfour := AK1_mulCount_lower ms h
  have hodd := AK1_mulCount_odd h
  exact ⟨by omega, AK1_conjCount_lower ms h, (AK_operation_bounds ms (h ▸ standard_hasIdentityExponents)).2⟩

/-- One nine-move witness attains all three bounds, and every ordinary path
from the ordered AK(1) pair to the ordered standard pair has length at least nine. -/
theorem AK1_distance_exact :
    (∃ ms : List (PrimitiveMove 2), runMoves (AK 1) ms = standard 2 ∧
      ms.length = 9 ∧ mulCount ms = 5 ∧ conjCount ms = 2) ∧
    (∀ ms : List (PrimitiveMove 2), runMoves (AK 1) ms = standard 2 → 9 ≤ ms.length) := by
  refine ⟨⟨AK1TwoConjugations, AK1_twoConjugations_witness.1, rfl, rfl, rfl⟩, ?_⟩
  intro ms h
  obtain ⟨_, _, _⟩ := AK1_min_operation_counts ms h
  omega

end AC
