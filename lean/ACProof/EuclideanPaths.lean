import ACProof.AK
import ACProof.EuclideanCost

/-!
# Multiplication counts for rank-two ordinary Andrews–Curtis paths

A homomorphism to the integers projects each pair of relators to a pair of
exponent sums. The subtractive Euclidean cost of their absolute values charges
only right multiplications. The other official moves leave it unchanged.
-/

namespace AC

open Function

/-- An official step with the number of right multiplications it uses. -/
inductive CountedStep {n : ℕ} : Relators n → Relators n → ℕ → Prop where
  | inv (R : Relators n) (i : Fin n) :
      CountedStep R (update R i (R i)⁻¹) 0
  | mulRight (R : Relators n) (i j : Fin n) (h : i ≠ j) :
      CountedStep R (update R i (R i * R j)) 1
  | conj (R : Relators n) (i : Fin n) (w : Word n) :
      CountedStep R (update R i (w * R i * w⁻¹)) 0

theorem CountedStep.step {n k : ℕ} {R S : Relators n} (h : CountedStep R S k) : Step R S := by
  cases h with
  | inv i => exact Step.inv _ i
  | mulRight i j hij => exact Step.mulRight _ i j hij
  | conj i w => exact Step.conj _ i w

theorem Step.exists_countedStep {n : ℕ} {R S : Relators n} (h : Step R S) :
    ∃ k, CountedStep R S k := by
  cases h with
  | inv i => exact ⟨0, .inv _ i⟩
  | mulRight i j hij => exact ⟨1, .mulRight _ i j hij⟩
  | conj i w => exact ⟨0, .conj _ i w⟩

/-- The last two indices count all steps and right multiplications, respectively. -/
inductive CountedPath {n : ℕ} (R : Relators n) : Relators n → ℕ → ℕ → Prop where
  | refl : CountedPath R R 0 0
  | tail {S T : Relators n} {l k c : ℕ} (p : CountedPath R S l k) (s : CountedStep S T c) :
      CountedPath R T (l + 1) (k + c)

theorem reachable_iff_exists_countedPath {n : ℕ} {R S : Relators n} :
    Reachable R S ↔ ∃ l k, CountedPath R S l k := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, 0, .refl⟩
    | tail _ s ih =>
      obtain ⟨l, k, p⟩ := ih
      obtain ⟨c, sc⟩ := s.exists_countedStep
      exact ⟨l + 1, k + c, p.tail sc⟩
  · rintro ⟨l, k, h⟩
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ s ih => exact Relation.ReflTransGen.tail ih s.step

theorem CountedPath.mulCount_le_length {n l k : ℕ} {R S : Relators n}
    (h : CountedPath R S l k) : k ≤ l := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ s ih => cases s <;> omega

/-- Potential for an arbitrary integral character of the ambient rank-two free group. -/
def euclideanPotential (χ : Word 2 →* Multiplicative ℤ) (R : Relators 2) : ℕ :=
  euclideanCost (χ (R 0)).toAdd.natAbs (χ (R 1)).toAdd.natAbs

theorem CountedStep.euclideanPotential_bound (χ : Word 2 →* Multiplicative ℤ)
    {R S : Relators 2} {c : ℕ} (h : CountedStep R S c) :
    euclideanPotential χ S ≤ euclideanPotential χ R + c ∧
    euclideanPotential χ R ≤ euclideanPotential χ S + c := by
  cases h with
  | inv i =>
    fin_cases i <;> simp [euclideanPotential]
  | conj i w =>
    fin_cases i <;> simp [euclideanPotential, mul_assoc]
  | mulRight i j hij =>
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [euclideanPotential] using
        euclideanCost_mulRight (χ (R 0)).toAdd (χ (R 1)).toAdd
    · simpa [euclideanPotential, add_comm] using
        And.intro (euclideanCost_add_right_le (χ (R 0)).toAdd (χ (R 1)).toAdd)
          (euclideanCost_le_add_right (χ (R 0)).toAdd (χ (R 1)).toAdd)
    · exact (hij rfl).elim

/-- The potential is 1-Lipschitz for each directed official move. -/
theorem Step.euclideanPotential_bound (χ : Word 2 →* Multiplicative ℤ)
    {R S : Relators 2} (h : Step R S) :
    euclideanPotential χ S ≤ euclideanPotential χ R + 1 ∧
    euclideanPotential χ R ≤ euclideanPotential χ S + 1 := by
  obtain ⟨c, hs⟩ := h.exists_countedStep
  obtain ⟨h₁, h₂⟩ := hs.euclideanPotential_bound χ
  have hc : c ≤ 1 := by cases hs <;> decide
  constructor <;> omega

/-- An endpoint potential difference in either direction bounds the multiplication count. -/
theorem CountedPath.euclideanPotential_bound (χ : Word 2 →* Multiplicative ℤ)
    {R S : Relators 2} {l k : ℕ} (h : CountedPath R S l k) :
    euclideanPotential χ S ≤ euclideanPotential χ R + k ∧
    euclideanPotential χ R ≤ euclideanPotential χ S + k := by
  induction h with
  | refl => simp
  | tail _ s ih =>
    obtain ⟨hs, hs'⟩ := s.euclideanPotential_bound χ
    obtain ⟨ha, ha'⟩ := ih
    constructor <;> omega

/-- Exponent sum of the generator y. -/
def expY : Word 2 →* Multiplicative ℤ := FreeGroup.lift ![1, Multiplicative.ofAdd 1]

theorem expY_gx : expY gx = 1 := by simp [expY, gx]
theorem expY_gy : expY gy = Multiplicative.ofAdd 1 := by simp [expY, gy]

theorem euclideanPotential_standard : euclideanPotential expY (standard 2) = 0 := by
  change euclideanCost (expY gx).toAdd.natAbs (expY gy).toAdd.natAbs = 0
  simp [expY_gx, expY_gy]

theorem euclideanPotential_AK (n : ℕ) : euclideanPotential expY (AK n) = n + 1 := by
  simp [euclideanPotential, AK, expY_gx, expY_gy, euclideanCost_one_right]
  rw [show -1 + -(n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring]
  exact (Int.natAbs_neg _).trans (Int.natAbs_natCast (n + 1))

/-- Any ordinary path from AK(n) to the standard pair uses at least n+1 right multiplications. -/
theorem AK_to_standard_mulCount {n l k : ℕ} (h : CountedPath (AK n) (standard 2) l k) :
    n + 1 ≤ k := by
  simpa [euclideanPotential_AK, euclideanPotential_standard] using
    (h.euclideanPotential_bound expY).2

/-- The same endpoint bound applies to paths starting at the standard pair. -/
theorem standard_to_AK_mulCount {n l k : ℕ} (h : CountedPath (standard 2) (AK n) l k) :
    n + 1 ≤ k := by
  simpa [euclideanPotential_AK, euclideanPotential_standard] using
    (h.euclideanPotential_bound expY).1

/-- A family obtained by successively right-multiplying the first relator by y. -/
def shearTuple (n : ℕ) : Relators 2 := ![gx * gy ^ n, gy]

private theorem euclideanPotential_shearTuple (n : ℕ) :
    euclideanPotential expY (shearTuple n) = n := by
  simp [euclideanPotential, shearTuple, expY_gx, expY_gy, euclideanCost_one_right]

/-- The explicit outgoing path achieves both the length and multiplication lower bounds. -/
theorem shearTuple_exact (n : ℕ) :
    CountedPath (standard 2) (shearTuple n) n n ∧
    ∀ {l k}, CountedPath (standard 2) (shearTuple n) l k → n ≤ k ∧ k ≤ l := by
  constructor
  · induction n with
    | zero =>
      have e : shearTuple 0 = standard 2 := by
        apply fin2_ext <;> simp [shearTuple, standard, gx, gy]
      rw [e]
      exact .refl
    | succ n ih =>
      have e : update (shearTuple n) 0 (shearTuple n 0 * shearTuple n 1) = shearTuple (n+1) := by
        apply fin2_ext <;> simp [shearTuple, pow_succ, mul_assoc]
      rw [← e]
      exact ih.tail (.mulRight _ 0 1 (by decide))
  · intro l k h
    exact ⟨by simpa [euclideanPotential_shearTuple, euclideanPotential_standard] using
      (h.euclideanPotential_bound expY).1, h.mulCount_le_length⟩

end AC
