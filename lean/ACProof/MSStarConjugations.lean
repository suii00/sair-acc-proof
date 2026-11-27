import ACProof.TwoInvolutions
import ACProof.MS1

/-! # Conjugation counts for the Miller–Schupp word y⁻¹xyx⁻¹ -/

namespace AC

namespace MSStarCertificate

private abbrev P := Equiv.Perm (Fin 4)
-- The cycles (0 3 1 2), (1 2) and (1 3), respectively.
private def x : P := Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 0 3
private def y : P := Equiv.swap 1 2
private def t : P := Equiv.swap 1 3
private def φ : Word 2 →* P := FreeGroup.lift ![x, y]

private theorem eval_x : φ gx = x := by simp [φ, gx]
private theorem eval_y : φ gy = y := by simp [φ, gy]

private theorem both_relators (n : ℕ) (hn : Odd n) :
    ∀ i, φ (MS n wstar i) = t := by
  obtain ⟨k, hk⟩ := hn
  have hy : y ^ 2 = 1 := by decide
  have hn' : n = 2*k + 1 := by omega
  have hp : y ^ n = y := by rw [hn', pow_succ, pow_mul, hy]; simp
  have hq : y ^ (n+1) = 1 := by rw [pow_succ, hp, ← pow_two, hy]
  intro i
  fin_cases i <;> simp [MS, wstar, eval_x, eval_y, hp, hq] <;> decide

/-- For every odd n, both relators have the same transposition as their image.
The squares of x and xy do not commute in this four-point permutation action. -/
theorem odd_lower {n : ℕ} (hn : Odd n) {ms : List (PrimitiveMove 2)}
    (h : runMoves (MS n wstar) ms = standard 2) : 2 ≤ conjCount ms := by
  by_contra! hc
  have ht : t ^ 2 = 1 := by decide
  obtain ⟨u, hu, hull⟩ := exists_involutions_of_atMostOneConj φ ht
    (fun i => Or.inr (both_relators n hn i)) ms (by omega)
  rw [h] at hull
  have hx := hull 0
  have hy := hull 1
  change φ gx ∈ _ at hx
  change φ gy ∈ _ at hy
  rw [eval_x] at hx
  rw [eval_y] at hy
  have hnc : ¬ Commute (x ^ 2) ((x * y) ^ 2) := by
    change x ^ 2 * (x * y) ^ 2 ≠ (x * y) ^ 2 * x ^ 2
    decide
  exact hnc (commute_sq_of_mem_closure_involutions ht hu hx (Subgroup.mul_mem _ hx hy))

end MSStarCertificate

/-- For n = 0 one conjugation turns the second relator, after a right
product, into xy⁻¹. Nielsen moves then finish at the ordered pair. -/
def msStarZeroMoves : List (PrimitiveMove 2) :=
  [.mulRight 1 0 (by decide), .conj 1 gx⁻¹, .inv 0, .mulRight 1 0 (by decide),
   .mulRight 0 1 (by decide), .inv 0, .mulRight 1 0 (by decide), .inv 1,
   .mulRight 0 1 (by decide), .inv 0]

theorem MSStar_zero_witness :
    runMoves (MS 0 wstar) msStarZeroMoves = standard 2 ∧ conjCount msStarZeroMoves = 1 := by
  refine ⟨?_, rfl⟩
  apply fin2_ext <;>
    simp [msStarZeroMoves, runMoves, PrimitiveMove.apply, MS, wstar, standard, gx, gy] <;> group

/-- A ten-move certificate for MS(1,y⁻¹xyx⁻¹), in chronological order. -/
def msStarOneMoves : List (PrimitiveMove 2) :=
  [.inv 0, .conj 0 (gy⁻¹ * gx), .mulRight 1 0 (by decide), .inv 0,
   .conj 1 (gy⁻¹ * gx⁻¹), .mulRight 0 1 (by decide), .inv 0,
   .conj 1 (gx⁻¹ * gy), .mulRight 1 0 (by decide), .inv 0]

theorem MSStar_one_witness :
    runMoves (MS 1 wstar) msStarOneMoves = standard 2 ∧
    conjCount msStarOneMoves = 3 ∧ msStarOneMoves.length = 10 := by
  refine ⟨?_, rfl, rfl⟩
  apply fin2_ext <;>
    simp [msStarOneMoves, runMoves, PrimitiveMove.apply, MS, wstar, standard, gx, gy] <;> group

end AC
