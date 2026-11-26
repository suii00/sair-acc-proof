import ACProof.AK1ConjLower
import ACProof.AK1ConjUpper
import ACProof.EuclideanWitness

/-! # Adding conjugation cost to the Akbulut–Kirby length bound -/

namespace AC

private def eraseConjugations {n : ℕ} : List (PrimitiveMove n) → List (PrimitiveMove n)
  | [] => []
  | .inv i :: ms => .inv i :: eraseConjugations ms
  | .mulRight i j h :: ms => .mulRight i j h :: eraseConjugations ms
  | .conj _ _ :: ms => eraseConjugations ms

private theorem eraseConjugations_length {n : ℕ} (ms : List (PrimitiveMove n)) :
    (eraseConjugations ms).length + conjCount ms = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => cases m <;> simp [eraseConjugations, conjCount, PrimitiveMove.conjCost] <;> omega

/-- Every integral character has the same endpoint after erasing all conjugations. -/
private theorem eraseConjugations_eval {n : ℕ} (χ : Word n →* Multiplicative ℤ)
    (ms : List (PrimitiveMove n)) {R S : Relators n} (h : ∀ i, χ (R i) = χ (S i)) :
    ∀ i, χ ((runMoves R ms) i) = χ ((runMoves S (eraseConjugations ms)) i) := by
  induction ms generalizing R S with
  | nil => exact h
  | cons m ms ih =>
    cases m with
    | inv i =>
      apply ih
      intro j
      by_cases hj : j = i
      · subst j; simp [PrimitiveMove.apply, h]
      · simpa [PrimitiveMove.apply, Function.update_of_ne hj] using h j
    | mulRight i j hij =>
      apply ih
      intro k
      by_cases hk : k = i
      · subst k; simp [PrimitiveMove.apply, h]
      · simpa [PrimitiveMove.apply, Function.update_of_ne hk] using h k
    | conj i w =>
      apply ih
      intro j
      by_cases hj : j = i
      · subst j; simp [PrimitiveMove.apply, h]
      · simpa [PrimitiveMove.apply, Function.update_of_ne hj] using h j

private theorem runMoves_counted {n : ℕ} (R : Relators n) (ms : List (PrimitiveMove n)) :
    CountedPath R (runMoves R ms) ms.length (mulCount ms) := by
  induction ms using List.reverseRecOn with
  | nil => exact .refl
  | append_singleton ms m ih =>
    rw [List.length_append, runMoves_append, mulCount_append]
    cases m with
    | inv i => exact ih.tail (.inv _ i)
    | mulRight i j hij => exact ih.tail (.mulRight _ i j hij)
    | conj i w => exact ih.tail (.conj _ i w)

/-- At least n+2 products and two inversions occur even after all conjugations are erased. -/
theorem AK_operation_bounds {n : ℕ} (ms : List (PrimitiveMove 2))
    (h : HasIdentityExponents (runMoves (AK n) ms)) :
    n + 2 ≤ mulCount ms ∧ mulCount ms + conjCount ms + 2 ≤ ms.length := by
  have he (χ : Word 2 →* Multiplicative ℤ) (i : Fin 2) :=
    congrArg Multiplicative.toAdd (eraseConjugations_eval χ ms (R := AK n) (S := AK n) (fun _ => rfl) i)
  have hf : HasIdentityExponents (runMoves (AK n) (eraseConjugations ms)) := by
    unfold HasIdentityExponents at h ⊢
    rwa [← he expX 0, ← he expY 0, ← he expX 1, ← he expY 1]
  obtain ⟨hmul, hinv⟩ := (AK_identityFiber_exact n).2 (runMoves_counted (AK n) _) hf
  have hm : mulCount (eraseConjugations ms) = mulCount ms := by
    clear h hf he hmul hinv
    induction ms with
    | nil => rfl
    | cons m ms ih => cases m <;> simp [eraseConjugations, mulCount, PrimitiveMove.mulCost, ih]
  have hlen := eraseConjugations_length ms
  omega

/-- The n+4 exponent-fiber lower bound is paid entirely by moves other than conjugations. -/
theorem AK_length_add_conjCount {n : ℕ} (ms : List (PrimitiveMove 2))
    (h : HasIdentityExponents (runMoves (AK n) ms)) : n + 4 + conjCount ms ≤ ms.length := by
  obtain ⟨_, _⟩ := AK_operation_bounds ms h
  omega

/-- Any ordinary AK(n) trivialization using at least two conjugations takes at least n+6 moves. -/
theorem AK_length_of_two_conjugations {n : ℕ} (ms : List (PrimitiveMove 2))
    (h : runMoves (AK n) ms = standard 2) (hc : 2 ≤ conjCount ms) : n + 6 ≤ ms.length := by
  have bound := AK_length_add_conjCount ms (h ▸ standard_hasIdentityExponents)
  omega

/-- The minimum number of arbitrary-word conjugations in an ordinary AK(1) trivialization is two. -/
theorem AK1_conjCount_exact :
    (∃ ms : List (PrimitiveMove 2), runMoves (AK 1) ms = standard 2 ∧ conjCount ms = 2) ∧
    (∀ ms : List (PrimitiveMove 2), runMoves (AK 1) ms = standard 2 → 2 ≤ conjCount ms) :=
  ⟨⟨AK1TwoConjugations, AK1_twoConjugations_witness.1, AK1_twoConjugations_witness.2.1⟩,
   AK1_conjCount_lower⟩

end AC
