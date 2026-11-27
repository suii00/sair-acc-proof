import ACProof.TwoInvolutions

/-! # A conjugation lower bound from complementary involution images

Before the first conjugation, each row has two bits recording its evaluations
in the two order-at-most-two subgroups. The pair of rows remains a basis over
the field with two elements. In at least one coordinate a row is zero; that
coordinate still has cyclic involution support after the first conjugation.
-/

namespace AC.ComplementaryInvolutions

abbrev Bits := Bool × Bool

private def addBits (a b : Bits) : Bits := (xor a.1 b.1, xor a.2 b.2)

private def basis (f : Fin 2 → Bits) : Bool :=
  f 0 != (false, false) && f 1 != (false, false) && f 0 != f 1

private theorem basis_add : ∀ (f : Fin 2 → Bits) (i j : Fin 2), i ≠ j →
    basis f → basis (Function.update f i (addBits (f i) (f j))) := by decide

private theorem zero_coordinate : ∀ f : Fin 2 → Bits, basis f →
    (∃ i, (f i).1 = false) ∨ (∃ i, (f i).2 = false) := by decide

private theorem other_bit : ∀ (b : Fin 2 → Bool), (∃ k, b k = false) →
    ∀ i, b i = true → ∀ j, j ≠ i → b j = false := by decide

variable {G H : Type*} [Group G] [Group H]

private def bitValue (s : G) (b : Bool) : G := if b then s else 1

private theorem bit_inv {s : G} (hs : s ^ 2 = 1) (a : Bool) :
    (bitValue s a)⁻¹ = bitValue s a := by
  have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hs)
  cases a <;> simp [bitValue, hi]

private theorem bit_mul {s : G} (hs : s ^ 2 = 1) (a b : Bool) :
    bitValue s a * bitValue s b = bitValue s (xor a b) := by
  cases a <;> cases b <;> simp [bitValue, ← pow_two, hs]

/-- In this image, the ordered target never belongs to a two-involution subgroup. -/
def ExcludesTarget (φ : Word 2 →* G) : Prop :=
  ∀ s t : G, s ^ 2 = 1 → t ^ 2 = 1 →
    (∀ i, φ (standard 2 i) ∈ Subgroup.closure ({s,t} : Set G)) → False

private theorem exclude_tail (φ : Word 2 →* G) (hx : ExcludesTarget φ)
    {s : G} (hs : s ^ 2 = 1) {R : Relators 2} (hR : ∀ i, φ (R i) = 1 ∨ φ (R i) = s)
    (ms : List (PrimitiveMove 2)) (hc : conjCount ms ≤ 1)
    (hend : runMoves R ms = standard 2) : False := by
  obtain ⟨t, ht, hi⟩ := exists_involutions_of_atMostOneConj φ hs hR ms hc
  rw [hend] at hi
  exact hx s t hs ht hi

private theorem cyclic_after_conj (φ : Word 2 →* G) {s : G} (hs : s ^ 2 = 1)
    {R : Relators 2} {b : Fin 2 → Bool} (hb : ∀ i, φ (R i) = bitValue s (b i))
    (hz : ∃ k, b k = false) (i : Fin 2) (w : Word 2) :
    ∃ u : G, u ^ 2 = 1 ∧ ∀ j, φ ((PrimitiveMove.conj i w).apply R j) = 1 ∨
      φ ((PrimitiveMove.conj i w).apply R j) = u := by
  cases hi : b i with
  | false =>
    refine ⟨s, hs, fun j => ?_⟩
    by_cases hj : j = i
    · subst j
      left
      simp [PrimitiveMove.apply, hb, hi, bitValue]
    · rw [PrimitiveMove.apply, Function.update_of_ne hj, hb]
      cases b j <;> simp [bitValue]
  | true =>
    refine ⟨φ w * s * (φ w)⁻¹, by simp [conj_pow, hs], fun j => ?_⟩
    by_cases hj : j = i
    · subst j
      right
      simp [PrimitiveMove.apply, hb, hi, bitValue]
    · left
      simp [PrimitiveMove.apply, Function.update_of_ne hj, hb,
        other_bit b hz i hi j hj, bitValue]

private theorem exclude_two (φ : Word 2 →* G) (ψ : Word 2 →* H)
    (exφ : ExcludesTarget φ) (exψ : ExcludesTarget ψ)
    {s : G} {t : H} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (ms : List (PrimitiveMove 2)) {R : Relators 2} {f : Fin 2 → Bits} (hf : basis f)
    (hφ : ∀ i, φ (R i) = bitValue s (f i).1)
    (hψ : ∀ i, ψ (R i) = bitValue t (f i).2)
    (hc : conjCount ms ≤ 2) (hend : runMoves R ms = standard 2) : False := by
  induction ms generalizing R f with
  | nil =>
    apply exclude_tail φ exφ hs (R := R) _ [] (by decide) hend
    intro i
    rw [hφ]
    cases (f i).1 <;> simp [bitValue]
  | cons m ms ih =>
    cases m with
    | inv i =>
      apply ih (f := f) hf (R := (PrimitiveMove.inv i).apply R) _ _ (by simpa [conjCount, PrimitiveMove.conjCost] using hc) hend
      all_goals
        intro j
        by_cases hj : j = i
        · subst j
          simp [PrimitiveMove.apply, hφ, hψ, bit_inv hs, bit_inv ht]
        · simp [PrimitiveMove.apply, Function.update_of_ne hj, hφ, hψ]
    | mulRight i j hij =>
      apply ih (basis_add f i j hij hf) (R := (PrimitiveMove.mulRight i j hij).apply R) _ _ (by simpa [conjCount, PrimitiveMove.conjCost] using hc) hend
      all_goals
        intro k
        by_cases hk : k = i
        · subst k
          simp [PrimitiveMove.apply, hφ, hψ, bit_mul hs, bit_mul ht, addBits]
        · simp [PrimitiveMove.apply, Function.update_of_ne hk, hφ, hψ]
    | conj i w =>
      change 1 + conjCount ms ≤ 2 at hc
      rcases zero_coordinate f hf with hz | hz
      · obtain ⟨u, hu, he⟩ := cyclic_after_conj φ hs hφ hz i w
        exact exclude_tail φ exφ hu he ms (by omega) hend
      · obtain ⟨u, hu, he⟩ := cyclic_after_conj ψ ht hψ hz i w
        exact exclude_tail ψ exψ hu he ms (by omega) hend

/-- If the two relators have respective images (s,1) and (1,t), where s,t
square to one, and each marked target excludes two-involution subgroups, then
any path to the ordered standard pair uses at least three conjugations. -/
theorem lower (φ : Word 2 →* G) (ψ : Word 2 →* H) {R : Relators 2}
    (hs : φ (R 0) ^ 2 = 1) (hφ : φ (R 1) = 1)
    (hψ : ψ (R 0) = 1) (ht : ψ (R 1) ^ 2 = 1)
    (exφ : ExcludesTarget φ) (exψ : ExcludesTarget ψ)
    (ms : List (PrimitiveMove 2)) (hend : runMoves R ms = standard 2) : 3 ≤ conjCount ms := by
  by_contra! hc
  let f : Fin 2 → Bits := ![(true, false), (false, true)]
  apply exclude_two φ ψ exφ exψ hs ht ms (f := f) (by decide) _ _ (by omega) hend
  · intro i
    fin_cases i <;> simp [f, bitValue, hφ]
  · intro i
    fin_cases i <;> simp [f, bitValue, hψ]

end AC.ComplementaryInvolutions
