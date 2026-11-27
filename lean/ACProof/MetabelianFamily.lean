import ACProof.MetabelianTwo

/-! Ordinary paths and marked evaluations for the family (x, y w^L). -/

namespace AC.MetabelianProbe

open scoped commutatorElement

private abbrev baseComm : Word 2 := ⁅gx, gy⁆
private abbrev conjugateComm : Word 2 := gx⁻¹ * baseComm * gx

private theorem law_eq : law = ⁅baseComm, conjugateComm⁆ := rfl

/-- The ordered pair Q_L. -/
def familyPair (L : ℕ) : Relators 2 := ![gx, gy * law ^ L]

/-- One block appends the inverse law to the second row and restores the first row. -/
private def removeBlock : List (PrimitiveMove 2) :=
  [.conj 0 conjugateComm, .mulRight 1 0 (by decide), .conj 0 conjugateComm⁻¹,
   .inv 0, .conj 0 (conjugateComm * gy), .mulRight 1 0 (by decide),
   .conj 0 (conjugateComm * gy)⁻¹, .inv 0,
   .conj 0 gy, .mulRight 1 0 (by decide), .conj 0 gy⁻¹,
   .inv 0, .mulRight 1 0 (by decide), .inv 0]

private theorem removeBlock_run (v : Word 2) :
    runMoves ![gx, v * law] removeBlock = ![gx, v] := by
  apply fin2_ext <;>
    simp [removeBlock, runMoves, PrimitiveMove.apply, law_eq, conjugateComm, baseComm,
      commutatorElement_def] <;> group

/-- A chronological ordinary trivialization of Q_L. -/
def familyMoves : ℕ → List (PrimitiveMove 2)
  | 0 => []
  | L + 1 => removeBlock ++ familyMoves L

/-- An explicit witness using exactly four positive right multiplications per block. -/
theorem family_witness (L : ℕ) :
    runMoves (familyPair L) (familyMoves L) = standard 2 ∧
    mulCount (familyMoves L) = 4 * L := by
  induction L with
  | zero =>
    refine ⟨?_, rfl⟩
    apply fin2_ext <;> simp [familyPair, familyMoves, runMoves, standard, gx, gy]
  | succ L ih =>
    have step : runMoves (familyPair (L + 1)) removeBlock = familyPair L := by
      simpa [familyPair, pow_succ, mul_assoc] using (removeBlock_run (gy * law ^ L))
    refine ⟨?_, ?_⟩
    · rw [familyMoves, runMoves_append, step, ih.1]
    · rw [familyMoves, mulCount_append, ih.2]
      have four : mulCount removeBlock = 4 := rfl
      omega

/-- Every marking into a group with abelian commutator subgroup gives the standard tuple. -/
theorem family_eval_metabelian {G : Type*} [Group G] [IsMulCommutative (commutator G)]
    (f : Word 2 →* G) (L : ℕ) : f ∘ familyPair L = f ∘ standard 2 := by
  have hc : f baseComm ∈ commutator G := by
    simpa only [baseComm, map_commutatorElement] using
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top (f gx)) (Subgroup.mem_top (f gy)))
  have hd : f conjugateComm ∈ commutator G := by
    simpa only [conjugateComm, map_mul, map_inv, inv_inv] using
      (Subgroup.Normal.conj_mem (inferInstance : (commutator G).Normal) (f baseComm) hc (f gx)⁻¹)
  have hw : f law = 1 := by
    rw [law_eq, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (mul_comm (⟨_, hc⟩ : commutator G) ⟨_, hd⟩)
  funext i
  fin_cases i <;> simp [familyPair, standard, gx, gy, hw]

end AC.MetabelianProbe
