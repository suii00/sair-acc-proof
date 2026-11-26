import ACProof.EuclideanSharp

/-!
# A path to the identity exponent matrix

The endpoint has the same four exponent sums as the ordered standard pair.
The construction gives a word-level path to that endpoint for every parameter.
-/

namespace AC

open Function

private theorem appendFirstMultiplications {R : Relators 2} {a b : Word 2} {l k : ℕ}
    (h : CountedPath R ![a, b] l k) (m : ℕ) :
    CountedPath R ![a * b ^ m, b] (l + m) (k + m) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have e : update (![a * b ^ m, b] : Relators 2) 0 ((a * b ^ m) * b) =
        ![a * b ^ (m + 1), b] := by
      apply fin2_ext <;> simp [pow_succ, mul_assoc]
    rw [← e]
    exact ih.tail (.mulRight _ 0 1 (by decide))

/-- Invert the second relator, multiply the first by it `n+1` times, invert the first
relator, and multiply the second by the first once. The four endpoint exponent sums
form the identity matrix, with `n+2` right multiplications among `n+4` moves. -/
theorem AK_identityExponentMatrix_witness (n : ℕ) :
    ∃ R : Relators 2, CountedPath (AK n) R (n + 4) (n + 2) ∧ HasIdentityExponents R := by
  let a := AK n 0
  let b := (AK n 1)⁻¹
  let c := (a * b ^ (n + 1))⁻¹
  have e₁ : update (AK n) 1 (AK n 1)⁻¹ = ![a, b] := by
    apply fin2_ext <;> simp [a, b]
  have h₁ : CountedPath (AK n) ![a, b] 1 0 := by
    rw [← e₁]
    exact CountedPath.refl.tail (.inv _ 1)
  have h₂ := appendFirstMultiplications h₁ (n + 1)
  have e₃ : update (![a * b ^ (n + 1), b] : Relators 2) 0 (a * b ^ (n + 1))⁻¹ =
      ![c, b] := by
    apply fin2_ext <;> simp [c]
  have h₃ := h₂.tail (.inv _ 0)
  change CountedPath _ (update _ 0 (a * b ^ (n + 1))⁻¹) _ _ at h₃
  rw [e₃] at h₃
  have e₄ : update (![c, b] : Relators 2) 1 (b * c) = ![c, b * c] := by
    apply fin2_ext <;> simp
  have h₄ := h₃.tail (.mulRight _ 1 0 (by decide))
  change CountedPath _ (update _ 1 (b * c)) _ _ at h₄
  rw [e₄] at h₄
  refine ⟨![c, b * c], ?_, ?_, ?_, ?_, ?_⟩
  · convert h₄ using 1 <;> omega
  all_goals simp [a, b, c, AK, expX, expY, gx, gy]

/-- The witness simultaneously minimizes the number of multiplications and the
total length of directed paths from `AK n` to a pair with identity exponent matrix. -/
theorem AK_identityFiber_exact (n : ℕ) :
    (∃ R : Relators 2, CountedPath (AK n) R (n + 4) (n + 2) ∧ HasIdentityExponents R) ∧
    (∀ {S : Relators 2} {l k : ℕ}, CountedPath (AK n) S l k → HasIdentityExponents S →
      n + 2 ≤ k ∧ k + 2 ≤ l) :=
  ⟨AK_identityExponentMatrix_witness n, fun p hS =>
    ⟨AK_to_identityFiber_mulCount p hS, AK_to_identityExponents_nonmul p hS⟩⟩

/-- Every directed ordinary path from `AK n` to the ordered standard pair takes at least
`n+4` steps. -/
theorem AK_to_standard_length {n l k : ℕ} (p : CountedPath (AK n) (standard 2) l k) :
    n + 4 ≤ l := by
  obtain ⟨hmul, hrest⟩ := (AK_identityFiber_exact n).2 p standard_hasIdentityExponents
  omega

end AC
