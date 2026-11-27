import ACProof.ConjugationTrace
import Mathlib.Tactic.Group

/-! The two-row induction step for the sharp cyclic rotation examples. -/

namespace AC.CyclicRelator

variable {n : ℕ} {i j : Fin n}

/-- Seven ordinary moves on the anchor row and one other row, in chronological order. -/
def recoveryMoves (i j : Fin n) (h : i ≠ j) : List (PrimitiveMove n) :=
  [.inv i, .mulRight i j h, .mulRight j i h.symm, .inv i,
   .inv j, .mulRight i j h, .inv j]

/-- A one-letter cyclic rotation from `zaz` to `azz` is undone by conjugation by `z`. -/
theorem undoRotation (R : Relators n) (j : Fin n) (a z : Word n)
    (hj : R j = a * z * z) :
    (PrimitiveMove.conj j z).apply R = Function.update R j (z * a * z) := by
  simp [PrimitiveMove.apply, hj, mul_assoc]

/-- In any rank, the block `(zazaz,zaz)` recovers `(a,z)` with no conjugations.
The equality of entire tuples also fixes the other rows. -/
theorem recoverRows (R : Relators n) (a z : Word n) (h : i ≠ j)
    (hi : R i = z * a * z * a * z) (hj : R j = z * a * z) :
    runMoves R (recoveryMoves i j h) = Function.update (Function.update R i a) j z ∧
      conjCount (recoveryMoves i j h) = 0 ∧ (recoveryMoves i j h).length = 7 := by
  refine ⟨?_, rfl, rfl⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [recoveryMoves, runMoves, PrimitiveMove.apply, h, h.symm, hi, hj]
    group
  by_cases hkj : k = j
  · subst k
    simp [recoveryMoves, runMoves, PrimitiveMove.apply, h, h.symm, hi, hj]
    group
  · simp [recoveryMoves, runMoves, PrimitiveMove.apply, hki, hkj]

end AC.CyclicRelator
