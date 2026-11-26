import ACProof.EuclideanPaths

/-! Determinant parity and the negative y-column constrain directed ordinary paths. -/

namespace AC

theorem expX_gx : expX gx = Multiplicative.ofAdd 1 := by simp [expX, gx]
theorem expX_gy : expX gy = 1 := by simp [expX, gy]

/-- The two abelianized relators, in their given order, form the identity matrix. -/
def HasIdentityExponents (R : Relators 2) : Prop :=
  (expX (R 0)).toAdd = 1 ∧ (expY (R 0)).toAdd = 0 ∧
  (expX (R 1)).toAdd = 0 ∧ (expY (R 1)).toAdd = 1

theorem standard_hasIdentityExponents : HasIdentityExponents (standard 2) := by
  change (expX gx).toAdd = 1 ∧ (expY gx).toAdd = 0 ∧
    (expX gy).toAdd = 0 ∧ (expY gy).toAdd = 1
  simp [expX_gx, expX_gy, expY_gx, expY_gy]

def exponentDet (R : Relators 2) : ℤ :=
  (expX (R 0)).toAdd * (expY (R 1)).toAdd - (expY (R 0)).toAdd * (expX (R 1)).toAdd

private def nonpositiveY (R : Relators 2) : Prop := ∀ i, (expY (R i)).toAdd ≤ 0

/-- The witness counts inversions along the given path. A zero count preserves
the nonpositive y-column, and the determinant records its parity. -/
private theorem CountedPath.orientation {R S : Relators 2} {l k : ℕ}
    (p : CountedPath R S l k) :
    ∃ j : ℕ, k + j ≤ l ∧ exponentDet S = (-1 : ℤ) ^ j * exponentDet R ∧
      (j = 0 → nonpositiveY R → nonpositiveY S) := by
  induction p with
  | refl => exact ⟨0, by simp, by simp, fun _ h => h⟩
  | tail _ s ih =>
    obtain ⟨j, hj, hd, hc⟩ := ih
    cases s with
    | inv i =>
      refine ⟨j + 1, by omega, ?_, by omega⟩
      rw [pow_succ, show ∀ a b : ℤ, a * -1 * b = -(a * b) by intros; ring, ← hd]
      fin_cases i <;> simp [exponentDet] <;> ring
    | mulRight i t hit =>
      refine ⟨j, by omega, ?_, ?_⟩
      · rw [← hd]
        fin_cases i <;> fin_cases t
        · exact (hit rfl).elim
        · simp [exponentDet]; ring
        · simp [exponentDet]; ring
        · exact (hit rfl).elim
      · intro hz hr a
        have hs := hc hz hr
        by_cases ha : a = i
        · subst a
          simpa using add_nonpos (hs i) (hs t)
        · simpa [Function.update_of_ne ha] using hs a
    | conj i w =>
      refine ⟨j, by omega, ?_, ?_⟩
      · rw [← hd]
        fin_cases i <;> simp [exponentDet, mul_comm]
      · intro hz hr a
        by_cases ha : a = i
        · subst a
          simpa [mul_comm] using hc hz hr i
        · simpa [Function.update_of_ne ha] using hc hz hr a

theorem AK_to_identityExponents_nonmul {n l k : ℕ} {S : Relators 2}
    (p : CountedPath (AK n) S l k) (hS : HasIdentityExponents S) : k + 2 ≤ l := by
  obtain ⟨hx₀, hy₀, hx₁, hy₁⟩ := hS
  have hd₀ : exponentDet (AK n) = 1 := by
    simp [exponentDet, AK, expX_gx, expX_gy, expY_gx, expY_gy]
  have hd₁ : exponentDet S = 1 := by simp [exponentDet, hx₀, hy₀, hx₁, hy₁]
  have hn : nonpositiveY (AK n) := by
    intro i
    fin_cases i <;> simp [AK, expY_gx, expY_gy]
  obtain ⟨j, hj, hd, hc⟩ := p.orientation
  have hnz : j ≠ 0 := by
    intro hz
    have h := hc hz hn 1
    rw [hy₁] at h
    omega
  have hn₁ : j ≠ 1 := by
    intro h
    simp [hd₀, hd₁, h] at hd
  omega

end AC
