import ACProof.ConjugationTrace
import ACProof.EuclideanOrientation
import Mathlib.Data.ZMod.Basic

/-! The sign of the exponent matrix on the three nonzero vectors of 𝔽₂²
records the parity of the number of directed right multiplications. -/

namespace AC

private abbrev F₂ := ZMod 2

/-- For an invertible binary matrix, `ab + bc + cd` is the parity of its
permutation of the three nonzero vectors. Adding either row to the other
changes this polynomial by `ad + bc`, the determinant in characteristic two. -/
private def binaryFrame (a b c d t : F₂) : Prop :=
  a * d + b * c = 1 ∧ a * b + b * c + c * d = t

private theorem binaryFrame_add :
    ∀ a b c d t : F₂, binaryFrame a b c d t →
      binaryFrame (a + c) (b + d) c d (t + 1) ∧
      binaryFrame a b (c + a) (d + b) (t + 1) := by
  unfold binaryFrame
  decide

private theorem binary_neg : ∀ x : F₂, -x = x := by decide

private def tupleFrame (R : Relators 2) (t : F₂) : Prop :=
  binaryFrame (expX (R 0)).toAdd (expY (R 0)).toAdd
    (expX (R 1)).toAdd (expY (R 1)).toAdd t

private theorem tupleFrame_move (R : Relators 2) (m : PrimitiveMove 2)
    {t : F₂} (h : tupleFrame R t) : tupleFrame (m.apply R) (t + m.mulCost) := by
  cases m with
  | inv i =>
    fin_cases i <;> simpa [tupleFrame, PrimitiveMove.apply, PrimitiveMove.mulCost, binary_neg] using h
  | conj i w =>
    fin_cases i <;> simpa [tupleFrame, PrimitiveMove.apply, PrimitiveMove.mulCost, mul_comm] using h
  | mulRight i j hij =>
    have hf := binaryFrame_add _ _ _ _ _ h
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [tupleFrame, PrimitiveMove.apply, PrimitiveMove.mulCost] using hf.1
    · simpa [tupleFrame, PrimitiveMove.apply, PrimitiveMove.mulCost] using hf.2
    · exact (hij rfl).elim

private theorem tupleFrame_run (R : Relators 2) (ms : List (PrimitiveMove 2))
    {t : F₂} (h : tupleFrame R t) : tupleFrame (runMoves R ms) (t + mulCount ms) := by
  induction ms generalizing R t with
  | nil => simpa [runMoves, mulCount] using h
  | cons m ms ih =>
    simpa [runMoves, mulCount, add_assoc] using ih (m.apply R) (tupleFrame_move R m h)

/-- Every trace taking AK(1) to the ordered standard pair contains an odd
number of right multiplications. -/
theorem AK1_mulCount_odd {ms : List (PrimitiveMove 2)}
    (h : runMoves (AK 1) ms = standard 2) : mulCount ms % 2 = 1 := by
  have initial : tupleFrame (AK 1) 1 := by
    norm_num [tupleFrame, binaryFrame, AK, expX_gx, expX_gy, expY_gx, expY_gy]
    decide
  have finish := tupleFrame_run _ ms initial
  rw [h] at finish
  have sign : (0 : F₂) = 1 + mulCount ms := by
    change binaryFrame (expX gx).toAdd (expY gx).toAdd (expX gy).toAdd
      (expY gy).toAdd (1 + mulCount ms) at finish
    simpa [expX_gx, expX_gy, expY_gx, expY_gy] using finish.2
  have one : (mulCount ms : F₂) = 1 := by
    have hsum := congrArg (fun x : F₂ => x - 1) sign
    simpa [binary_neg] using hsum.symm
  simpa [ZMod.val_natCast] using congrArg ZMod.val one

end AC
