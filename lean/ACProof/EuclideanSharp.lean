import ACProof.EuclideanOrientation

/-!
# A strict multiplication bound for Akbulut–Kirby paths

Equality in the Euclidean bound forces every multiplication to lower the
potential. A second row with unit exponent sums in both coordinates then
either retains both magnitudes or reaches zero in the y-coordinate.
-/

namespace AC

open Function

private theorem euclideanCost_consecutive (a : ℕ) (ha : 0 < a) :
    euclideanCost (a + 1) a = a + 1 := by
  calc
    euclideanCost (a + 1) a = euclideanCost (1 + a) a := by rw [Nat.add_comm a 1]
    _ = euclideanCost 1 a + 1 := euclideanCost_add_left 1 a ha
    _ = a + 1 := by rw [euclideanCost_comm 1 a, euclideanCost_one_right]

/-- With a unit second coordinate, updating it can strictly lower the
potential only by cancelling it. -/
private theorem unit_descent_cancels (a v : ℤ) (hv : v.natAbs = 1)
    (h : a.natAbs = euclideanCost a.natAbs (v + a).natAbs + 1) : (v + a).natAbs = 0 := by
  by_contra hn
  have ha : 0 < a.natAbs := by omega
  have hc : 0 < (v + a).natAbs := by omega
  have adjacent : (v + a).natAbs = a.natAbs + 1 ∨ a.natAbs = (v + a).natAbs + 1 := by
    rcases Int.natAbs_eq a with h₁ | h₁ <;> rcases Int.natAbs_eq v with h₂ | h₂ <;>
      rcases Int.natAbs_eq (v + a) with h₃ | h₃ <;> omega
  rcases adjacent with e | e
  · have c := euclideanCost_consecutive a.natAbs ha
    rw [← e, euclideanCost_comm] at c
    omega
  · have c := euclideanCost_consecutive (v + a).natAbs hc
    rw [← e] at c
    omega

private def unitOrZero (χ : Word 2 →* Multiplicative ℤ) (R : Relators 2) : Prop :=
  ((χ (R 1)).toAdd.natAbs = 1 ∧ (expY (R 1)).toAdd.natAbs = 1) ∨
    (expY (R 1)).toAdd.natAbs = 0

private theorem unitOrZero_step (χ : Word 2 →* Multiplicative ℤ)
    {R S : Relators 2} {c : ℕ} (s : CountedStep R S c) (h : unitOrZero χ R)
    (desc : euclideanPotential expY R = euclideanPotential expY S + c) : unitOrZero χ S := by
  cases s with
  | inv i => fin_cases i <;> simpa [unitOrZero] using h
  | conj i w => fin_cases i <;> simpa [unitOrZero, mul_assoc] using h
  | mulRight i j hij =>
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [unitOrZero] using h
    · right
      rcases h with ⟨_, hy⟩ | hy
      · simp [euclideanPotential, hy] at desc
        simpa using unit_descent_cancels (expY (R 0)).toAdd (expY (R 1)).toAdd hy desc
      · simp [euclideanPotential, hy] at desc
    · exact (hij rfl).elim

private theorem unitOrZero_path (χ : Word 2 →* Multiplicative ℤ)
    {R S : Relators 2} {l k : ℕ} (p : CountedPath R S l k) (h : unitOrZero χ R)
    (desc : euclideanPotential expY R = euclideanPotential expY S + k) : unitOrZero χ S := by
  induction p with
  | refl => exact h
  | tail p s ih =>
    have hp := (p.euclideanPotential_bound expY).2
    have hs := (s.euclideanPotential_bound expY).2
    exact unitOrZero_step χ s (ih (by omega)) (by omega)

/-- A change in a second character at the unit second row forces strict slack
in the Euclidean estimate whenever the final y-coordinate there is nonzero. -/
theorem CountedPath.strict_euclideanPotential_bound (χ : Word 2 →* Multiplicative ℤ)
    {R S : Relators 2} {l k : ℕ} (p : CountedPath R S l k)
    (hx : (χ (R 1)).toAdd.natAbs = 1) (hy : (expY (R 1)).toAdd.natAbs = 1)
    (hx' : (χ (S 1)).toAdd.natAbs ≠ 1) (hy' : (expY (S 1)).toAdd.natAbs ≠ 0) :
    euclideanPotential expY R < euclideanPotential expY S + k := by
  have bound := (p.euclideanPotential_bound expY).2
  by_contra! h
  rcases unitOrZero_path χ p (Or.inl ⟨hx, hy⟩) (by omega) with ⟨hx₁, _⟩ | hy₁
  · exact hx' hx₁
  · exact hy' hy₁

/-- Only three entries of the target exponent matrix are required for the bound. -/
theorem AK_to_identityExponents_mulCount {n l k : ℕ} {S : Relators 2}
    (p : CountedPath (AK n) S l k) (hy₀ : (expY (S 0)).toAdd = 0)
    (hy₁ : (expY (S 1)).toAdd = 1) (hx₁ : (expX (S 1)).toAdd = 0) : n + 2 ≤ k := by
  have strict := p.strict_euclideanPotential_bound expX
    (by simp [AK, expX_gx, expX_gy]) (by simp [AK, expY_gx, expY_gy])
    (by simp [hx₁]) (by simp [hy₁])
  have terminal : euclideanPotential expY S = 0 := by simp [euclideanPotential, hy₀]
  rw [euclideanPotential_AK, terminal, zero_add] at strict
  omega

theorem AK_to_identityFiber_mulCount {n l k : ℕ} {S : Relators 2}
    (p : CountedPath (AK n) S l k) (hS : HasIdentityExponents S) : n + 2 ≤ k :=
  AK_to_identityExponents_mulCount p hS.2.1 hS.2.2.2 hS.2.2.1

/-- Every ordinary path to the ordered standard pair uses at least n+2 multiplications. -/
theorem AK_to_standard_mulCount_sharp {n l k : ℕ} (p : CountedPath (AK n) (standard 2) l k) :
    n + 2 ≤ k := AK_to_identityFiber_mulCount p standard_hasIdentityExponents

end AC
