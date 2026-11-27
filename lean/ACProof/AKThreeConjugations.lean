import ACProof.AKProjective
import ACProof.ComplementaryInvolutions

/-! # A uniform three-conjugation obstruction for AK(n), n ≥ 2

The complementary marking uses coordinate swap and horizontal shear on vectors
over Z/m, where m is the odd member of n, n+1. Its first relator is trivial.
-/

namespace AC.AKThreeConjugations

private abbrev Plane (R : Type) := R × R

private def swapXY (R : Type) : Equiv.Perm (Plane R) := Equiv.prodComm R R

private def shear {R : Type} [CommRing R] (k : R) : Equiv.Perm (Plane R) where
  toFun p := (p.1 + k * p.2, p.2)
  invFun p := (p.1 - k * p.2, p.2)
  left_inv := by rintro ⟨a,b⟩; simp
  right_inv := by rintro ⟨a,b⟩; simp

private theorem shear_pow {R : Type} [CommRing R] (k : R) (n : ℕ) :
    shear k ^ n = shear (n * k) := by
  induction n with
  | zero =>
    rw [pow_zero]
    ext p
    all_goals simp [shear]
  | succ n ih =>
    rw [pow_succ, ih]
    apply Equiv.ext
    rintro ⟨a,b⟩
    apply Prod.ext
    · change a + k * b + n * k * b = a + (↑(n+1) : R) * k * b
      push_cast; ring
    · rfl

private theorem shear_period (m : ℕ) : shear (1 : ZMod m) ^ m = 1 := by
  rw [shear_pow, ZMod.natCast_self, zero_mul]
  ext p <;> simp [shear]

private theorem swap_even (R : Type) (k : ℕ) : swapXY R ^ (2*k) = 1 := by
  have hh : swapXY R ^ 2 = 1 := by
    rw [pow_two]
    rfl
  rw [pow_mul, hh, one_pow]

private theorem defect_sq {R : Type} [CommRing R] :
    ((swapXY R * shear (1 : R) * swapXY R) * (shear (1 : R) * swapXY R * shear (1 : R))⁻¹)^2 = 1 := by
  apply Equiv.ext
  rintro ⟨a,b⟩
  apply Prod.ext <;>
    simp [pow_two, Equiv.Perm.mul_apply, mul_inv_rev, swapXY, shear]

private theorem separated {m : ℕ} (hm : 2 < m) :
    ¬ Commute ((shear (1 : ZMod m)) ^ 2)
      ((swapXY (ZMod m) * shear (1 : ZMod m)) ^ 2) := by
  intro hc
  have h := congrArg Prod.fst (DFunLike.congr_fun hc.eq (1,0))
  simp [pow_two, Equiv.Perm.mul_apply, swapXY, shear] at h
  have hn : (2 : ZMod m) ≠ 0 := by
    change ((2 : ℕ) : ZMod m) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) hm
  apply hn
  linear_combination h

private def mark {P : Type} (X Y : Equiv.Perm P) : Word 2 →* Equiv.Perm P :=
  FreeGroup.lift ![X,Y]

@[simp] private theorem mark_x {P : Type} (X Y : Equiv.Perm P) : mark X Y gx = X := by
  simp [mark, gx]
@[simp] private theorem mark_y {P : Type} (X Y : Equiv.Perm P) : mark X Y gy = Y := by
  simp [mark, gy]

private theorem complement (n : ℕ) (hn : 2 ≤ n) :
    ∃ (P : Type) (φ : Word 2 →* Equiv.Perm P),
      φ (AK n 0) = 1 ∧ φ (AK n 1) ^ 2 = 1 ∧ ComplementaryInvolutions.ExcludesTarget φ := by
  by_cases parity : n % 2 = 0
  · let R := ZMod (n+1)
    let U := swapXY R
    let V := shear (1 : R)
    have hu : U ^ n = 1 := by
      have h : n = 2*(n/2) := by omega
      conv_lhs => rw [h]
      exact swap_even R _
    refine ⟨_, mark U V, ?_, ?_, ?_⟩
    · simp [AK, hu, V, R, shear_period]
    · simpa [AK, U, V] using (defect_sq (R := R))
    · intro s t hs ht hall
      have hU : U ∈ Subgroup.closure ({s,t} : Set _) := by
        simpa [standard, mark] using hall 0
      have hV : V ∈ Subgroup.closure ({s,t} : Set _) := by
        simpa [standard, mark] using hall 1
      exact separated (m := n+1) (by omega)
        (commute_sq_of_mem_closure_involutions hs ht hV (Subgroup.mul_mem _ hU hV))
  · let R := ZMod n
    let U := swapXY R
    let V := shear (1 : R)
    have hu : U ^ (n+1) = 1 := by
      have h : n+1 = 2*((n+1)/2) := by omega
      conv_lhs => rw [h]
      exact swap_even R _
    refine ⟨_, mark V U, ?_, ?_, ?_⟩
    · simp [AK, hu, V, R, shear_period]
    · have hd := defect_sq (R := R)
      have hi := congrArg (fun z : Equiv.Perm (Plane R) => z⁻¹) hd
      simpa [AK, U, V, ← inv_pow, mul_inv_rev] using hi
    · intro s t hs ht hall
      have hV : V ∈ Subgroup.closure ({s,t} : Set _) := by
        simpa [standard, mark] using hall 0
      have hU : U ∈ Subgroup.closure ({s,t} : Set _) := by
        simpa [standard, mark] using hall 1
      exact separated (m := n) (by omega)
        (commute_sq_of_mem_closure_involutions hs ht hV (Subgroup.mul_mem _ hU hV))

/-- For n ≥ 2 every directed ordinary trivialization uses three or more
arbitrary-word conjugations. No existence hypothesis beyond the given path. -/
theorem _root_.AC.AK_three_conjugations {n : ℕ} (hn : 2 ≤ n) (ms : List (PrimitiveMove 2))
    (hend : runMoves (AK n) ms = standard 2) : 3 ≤ conjCount ms := by
  obtain ⟨P, φ, h0, h1, hnc⟩ := AKProjective.exists_marking (n := n) (by omega)
  obtain ⟨Q, ψ, k0, k1, exψ⟩ := complement n hn
  apply ComplementaryInvolutions.lower φ ψ h0 h1 k0 k1 _ exψ ms hend
  intro s t hs ht hall
  exact hnc (commute_sq_of_mem_closure_involutions hs ht (hall 0)
    (Subgroup.mul_mem _ (hall 0) (hall 1)))

/-- A consequence of the separate nonconjugation cost and the three-conjugation bound. -/
theorem _root_.AC.AK_length_add_seven {n : ℕ} (hn : 2 ≤ n) (ms : List (PrimitiveMove 2))
    (hend : runMoves (AK n) ms = standard 2) : n + 7 ≤ ms.length := by
  have hc := AK_three_conjugations hn ms hend
  have hl := AK_length_add_conjCount ms (hend ▸ standard_hasIdentityExponents)
  omega

end AC.AKThreeConjugations
