import ACProof.TwoInvolutions
import ACProof.ConjugationLength
import Mathlib.Data.ZMod.Basic

/-! The braid representation on vectors modulo simultaneous negation.
This construction also works over composite residue rings. -/

namespace AC.AKProjective

private def signs (R : Type*) [AddCommGroup R] : Setoid (R × R) where
  r u v := v = u ∨ v = -u
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by rintro _ _ (rfl | rfl) <;> simp
    trans := by rintro _ _ _ (rfl | rfl) (rfl | rfl) <;> simp }

private abbrev Plane (R : Type*) [AddCommGroup R] := Quotient (signs R)
private def point {R : Type*} [AddCommGroup R] (u v : R) : Plane R :=
  Quotient.mk _ (u, v)

private def descend {R : Type*} [AddCommGroup R] (f : R × R → R × R)
    (hf : ∀ p, f (-p) = -f p) : Plane R → Plane R :=
  Quotient.map f (by
    rintro a b (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (hf a))

variable {R : Type*} [CommRing R]

private def upperMap (k : R) : Plane R → Plane R :=
  descend (fun p => (p.1 + k * p.2, p.2)) (by rintro ⟨a, b⟩; simp [add_comm])
private def lowerMap (k : R) : Plane R → Plane R :=
  descend (fun p => (p.1, p.2 + k * p.1)) (by rintro ⟨a, b⟩; simp [add_comm])

private def upper (k : R) : Equiv.Perm (Plane R) where
  toFun := upperMap k
  invFun := upperMap (-k)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p => rcases p with ⟨a, b⟩; change point (a + k * b + -k * b) b = point a b; simp
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p => rcases p with ⟨a, b⟩; change point (a + -k * b + k * b) b = point a b; simp

private def lower (k : R) : Equiv.Perm (Plane R) where
  toFun := lowerMap k
  invFun := lowerMap (-k)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p => rcases p with ⟨a, b⟩; change point a (b + k * a + -k * a) = point a b; simp
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ p => rcases p with ⟨a, b⟩; change point a (b + -k * a + k * a) = point a b; simp

private theorem upper_pow (k : R) (n : ℕ) : upper k ^ n = upper (n * k) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero]
    ext q
    induction q using Quotient.inductionOn with
    | _ p => rcases p with ⟨a, b⟩; change point a b = point (a + (0 : R) * k * b) b; simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext q
    induction q using Quotient.inductionOn with
    | _ p =>
      rcases p with ⟨a, b⟩
      change point (a + k * b + n * k * b) b = point (a + (↑(n + 1) : R) * k * b) b
      push_cast; ring_nf

private theorem lower_pow (k : R) (n : ℕ) : lower k ^ n = lower (n * k) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero]
    ext q
    induction q using Quotient.inductionOn with
    | _ p => rcases p with ⟨a, b⟩; change point a b = point a (b + (0 : R) * k * a); simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext q
    induction q using Quotient.inductionOn with
    | _ p =>
      rcases p with ⟨a, b⟩
      change point a (b + k * a + n * k * a) = point a (b + (↑(n + 1) : R) * k * a)
      push_cast; ring_nf

private abbrev X (R : Type*) [CommRing R] := upper (1 : R)
private abbrev Y (R : Type*) [CommRing R] := lower (-1 : R)

@[simp] private theorem X_point (a b : R) : X R (point a b) = point (a + b) b := by
  change point (a + 1 * b) b = point (a + b) b
  rw [one_mul]

@[simp] private theorem Y_point (a b : R) : Y R (point a b) = point a (b - a) := by
  change point a (b + (-1) * a) = point a (b - a)
  simp [sub_eq_add_neg]

private theorem braid : X R * Y R * X R = Y R * X R * Y R := by
  ext q
  induction q using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨a, b⟩
    change (X R * Y R * X R) (point a b) = (Y R * X R * Y R) (point a b)
    simp only [Equiv.Perm.mul_apply, X_point, Y_point]
    ring_nf

private abbrev modulus (n : ℕ) := n * (n + 1) + 2

private theorem trace_zero (n : ℕ) : (n : ZMod (modulus n)) * ((n : ZMod (modulus n)) + 1) + 2 = 0 := by
  have h := ZMod.natCast_self (modulus n)
  simpa only [modulus, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using h

/-- The first relator matrix has determinant one and trace zero in this ring.
Coordinatewise Cayley–Hamilton gives minus the input vector upon squaring. -/
private theorem first_sq (n : ℕ) :
    (X (ZMod (modulus n)) ^ n * (Y (ZMod (modulus n)) ^ (n + 1))⁻¹) ^ 2 = 1 := by
  let A := ZMod (modulus n)
  rw [upper_pow, lower_pow, pow_two]
  ext q
  induction q using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨a, b⟩
    let k : A := n
    have hkj : k * (k + 1) + 2 = 0 := trace_zero n
    let d : A := -(((n + 1 : ℕ) : A) * (-1))
    have hd : d = k + 1 := by dsimp [d, k]; push_cast; ring
    change point ((a + k * 1 * (b + d * a)) + k * 1 * ((b + d * a) + d * (a + k * 1 * (b + d * a))))
      ((b + d * a) + d * (a + k * 1 * (b + d * a))) = point a b
    rw [hd]
    apply Quotient.sound
    right
    apply Prod.ext
    · dsimp
      linear_combination (a + k * (b + (k + 1) * a)) * hkj
    · dsimp
      linear_combination (b + (k + 1) * a) * hkj

/-- Evaluate both products on the second standard vector. Its two image
classes have second coordinate zero and minus two, even after a sign change. -/
private theorem squares_not_commute (n : ℕ) (hn : 0 < n) :
    ¬ Commute (X (ZMod (modulus n)) ^ 2)
      ((X (ZMod (modulus n)) * Y (ZMod (modulus n))) ^ 2) := by
  let A := ZMod (modulus n)
  intro hc
  have he := DFunLike.congr_fun hc.eq (point (0 : A) 1)
  simp only [pow_two, Equiv.Perm.mul_apply, X_point, Y_point] at he
  have hv := Quotient.exact he
  rcases hv with hp | hp <;> have hz := congrArg Prod.snd hp <;> dsimp at hz
  all_goals
    have htwo : (2 : ZMod (modulus n)) ≠ 0 := by
      change ((2 : ℕ) : ZMod (modulus n)) ≠ 0
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by decide) (by dsimp [modulus]; nlinarith)
    apply htwo
    linear_combination -hz

private def character (n : ℕ) : Word 2 →* Equiv.Perm (Plane (ZMod (modulus n))) :=
  FreeGroup.lift ![X (ZMod (modulus n)), Y (ZMod (modulus n))]

private theorem char_x (n : ℕ) : character n gx = X (ZMod (modulus n)) := by
  simp [character, gx]
private theorem char_y (n : ℕ) : character n gy = Y (ZMod (modulus n)) := by
  simp [character, gy]

/-- Every ordinary path from AK(n) to the ordered standard pair needs at least two
conjugations, counting one for an arbitrary word. -/
theorem _root_.AC.AK_two_conjugations {n : ℕ} (hn : 0 < n) (ms : List (PrimitiveMove 2))
    (hend : runMoves (AK n) ms = standard 2) : 2 ≤ conjCount ms := by
  apply two_le_conjCount_of_involutionImage (character n) _ _ _ hend
  · simpa [AK, char_x, char_y] using first_sq n
  · simp [AK, char_x, char_y, braid]
  · simpa [char_x, char_y] using squares_not_commute n hn

/-- The two conjugations add to the directed identity-exponent distance.
Existence of a path is the hypothesis, for each positive parameter. -/
theorem _root_.AC.AK_length_add_six {n : ℕ} (hn : 0 < n) (ms : List (PrimitiveMove 2))
    (hend : runMoves (AK n) ms = standard 2) : n + 6 ≤ ms.length :=
  AK_length_of_two_conjugations ms hend (AK_two_conjugations hn ms hend)

end AC.AKProjective
