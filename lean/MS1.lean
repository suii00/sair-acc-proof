import ACProof.Basic
import ACProof.MillerSchupp

/-!
# Shehper et al. (arXiv:2408.15332v2) Theorem B(i), B(ii)

* `MS1_reachable`  : `MS(1, w)` is AC-trivial for every `w` with x-exponent sum 0
                      (their Theorem 2).
* `MS_wstar_reachable` : `MS(n, y⁻¹ x y x⁻¹)` is AC-trivial for every `n`
                      (their Theorem 3).

Convention: `MS n w = ![x⁻¹ yⁿ x y^{-(n+1)}, x w⁻¹]` (see `ACProof/MillerSchupp.lean`),
matching `MS(n,w) = ⟨x,y | x⁻¹yⁿx = y^{n+1}, x = w⟩`.
-/

namespace AC
open Function

/-- Exponent sum in `x`, as a hom to `Multiplicative ℤ`. -/
def expX : Word 2 →* Multiplicative ℤ := FreeGroup.lift ![Multiplicative.ofAdd 1, 1]

section Normal
variable {Q : Type*} [Group Q] (X Y : Q)

/-- `T a b = X^a Y^b X^{-a}` -/
def T (a : ℕ) (b : ℤ) : Q := X ^ (a : ℤ) * Y ^ b * X ^ (-(a : ℤ))

variable {X Y}
variable (hrel : X⁻¹ * Y * X = Y ^ (2 : ℤ))
include hrel

theorem conjY (b : ℤ) : X⁻¹ * Y ^ b * X = Y ^ (2 * b) := by
  have h := conj_zpow (a := X⁻¹) (b := Y) (i := b)
  simp only [inv_inv] at h
  rw [← h, hrel, ← zpow_mul]

theorem T_succ (a : ℕ) (b : ℤ) : T X Y a b = T X Y (a + 1) (2 * b) := by
  unfold T
  rw [← conjY hrel b]
  push_cast
  group

theorem T_lift (a c : ℕ) (b : ℤ) : T X Y a b = T X Y (a + c) (2 ^ c * b) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [ih, T_succ hrel, pow_succ]
    (congr 1; try ring)

omit hrel in
theorem T_mul_same (a : ℕ) (b d : ℤ) : T X Y a b * T X Y a d = T X Y a (b + d) := by
  unfold T; group

theorem T_mul (a c : ℕ) (b d : ℤ) : ∃ e f, T X Y a b * T X Y c d = T X Y e f := by
  refine ⟨a + c, 2 ^ c * b + 2 ^ a * d, ?_⟩
  rw [T_lift hrel a c b, T_lift hrel c a d, add_comm c a, T_mul_same]

theorem conj_neg (k : ℕ) (d : ℤ) :
    X ^ (-(k : ℤ)) * Y ^ d * X ^ (k : ℤ) = Y ^ (2 ^ k * d) := by
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
    have e : X ^ (-((k + 1 : ℕ) : ℤ)) * Y ^ d * X ^ ((k + 1 : ℕ) : ℤ)
        = X⁻¹ * (X ^ (-(k : ℤ)) * Y ^ d * X ^ (k : ℤ)) * X := by push_cast; group
    rw [e, ih, conjY hrel, pow_succ]; congr 1; ring

theorem conj_T (m : ℤ) (d : ℤ) : ∃ a b, X ^ m * Y ^ d * X ^ (-m) = T X Y a b := by
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · exact ⟨k, d, rfl⟩
  · refine ⟨0, 2 ^ k * d, ?_⟩
    rw [neg_neg, conj_neg hrel]; simp [T]

theorem conj_TT (m : ℤ) (a : ℕ) (b : ℤ) :
    ∃ e f, X ^ m * T X Y a b * X ^ (-m) = T X Y e f := by
  obtain ⟨e, f, h⟩ := conj_T hrel (m + a) b
  refine ⟨e, f, ?_⟩
  rw [← h]; unfold T; group

end Normal

section MS1
local notation "N1" => Subgroup.normalClosure ({MS 1 (1 : Word 2) 0} : Set (Word 2))
local notation "mk" => (QuotientGroup.mk : Word 2 → Word 2 ⧸ N1)

theorem hrel1 : (mk gx)⁻¹ * mk gy * mk gx = (mk gy) ^ (2 : ℤ) := by
  have h : mk (MS 1 (1 : Word 2) 0) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
  simp only [MS, Matrix.cons_val_zero, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_pow] at h
  have h2 := mul_inv_eq_one.mp h
  simpa using h2

/-- Normal form in `BS(1,2)`: every word is `X^a Y^b X^{-a} X^{e}`, `e` its x-exponent sum. -/
theorem normal_form (g : Word 2) :
    ∃ a b, mk g = T (mk gx) (mk gy) a b * (mk gx) ^ (Multiplicative.toAdd (expX g)) := by
  induction g using FreeGroup.induction_on with
  | C1 => exact ⟨0, 0, by simp [T]⟩
  | of i =>
    fin_cases i
    · exact ⟨0, 0, by simp [T, expX]⟩
    · exact ⟨0, 1, by simp [T, expX]⟩
  | inv_of i ih =>
    fin_cases i
    · exact ⟨0, 0, by simp [T, expX]⟩
    · exact ⟨0, -1, by simp [T, expX]⟩
  | mul g h ihg ihh =>
    obtain ⟨a, b, hg⟩ := ihg
    obtain ⟨c, d, hh⟩ := ihh
    obtain ⟨c', d', hc⟩ := conj_TT hrel1 (Multiplicative.toAdd (expX g)) c d
    obtain ⟨a', b', ha⟩ := T_mul hrel1 a c' b d'
    refine ⟨a', b', ?_⟩
    rw [QuotientGroup.mk_mul, hg, hh, ← ha, ← hc, map_mul, toAdd_mul, zpow_add]
    group

/-- **Shehper et al. Theorem 2.** `MS(1, w)` is AC-trivial whenever `w` has
x-exponent sum zero. -/
theorem MS1_reachable (w : Word 2) (hw : expX w = 1) : Reachable (MS 1 w) (standard 2) := by
  obtain ⟨a, b, hab⟩ := normal_form w
  rw [hw, toAdd_one, zpow_zero, mul_one] at hab
  set v : Word 2 := gx ^ (a : ℤ) * gy ^ (-b) * gx ^ (-(a : ℤ))
  have s1 : Reachable (MS 1 w) ![MS 1 w 0, gx * v] := by
    refine reach_of_mul _ _ (i := 1) (j := 0) (by decide) (w * v) ?_ ?_
    · have e : MS 1 w 0 = MS 1 (1 : Word 2) 0 := rfl
      rw [e, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hab]
      simp only [v, T, QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      group
    · refine fin2_ext rfl ?_
      simp [MS]
  have s2 : Reachable ![MS 1 w 0, gx * v] (MS 1 (gy ^ b)) :=
    reach_of_conj _ _ 1 (gx ^ (-(a : ℤ))) (by
      refine fin2_ext rfl ?_
      simp only [MS, update_self, v, Matrix.cons_val_one, Matrix.cons_val_zero]
      group)
  exact s1.trans' (s2.trans' (MS_ypow_reachable 1 b))

/-- `w⋆ = y⁻¹ x y x⁻¹` -/
abbrev wstar : Word 2 := gy⁻¹ * gx * gy * gx⁻¹

/-- **Shehper et al. Theorem 3.** `MS(n, y⁻¹ x y x⁻¹)` is AC-trivial for every `n`. -/
theorem MS_wstar_reachable (n : ℕ) : Reachable (MS n wstar) (standard 2) := by
  set w' : Word 2 := gy⁻¹ * gx ^ n * gy * (gx ^ n)⁻¹
  have hw' : expX w' = 1 := by simp [w', expX]
  have hB := MS1_reachable w' hw'
  set B := MS 1 w'
  set A : Relators 2 := ![(B 1)⁻¹, (B 0)⁻¹]
  -- A → B ∘ swap → B → standard
  have hA : Reachable A (standard 2) := by
    have t1 := reach_inv A 0
    have t2 := reach_inv (update A 0 (A 0)⁻¹) 1
    have e : update (update A 0 (A 0)⁻¹) 1 ((update A 0 (A 0)⁻¹) 1)⁻¹ = B ∘ Equiv.swap 0 1 := by
      apply fin2_ext <;> simp [A]
    have t3 := (reach_perm B (Equiv.swap 0 1)).symm
    exact t1.trans' ((e ▸ t2).trans' (t3.trans' hB))
  have h := hA.relabel (Equiv.swap 0 1)
  have e : FreeGroup.map (Equiv.swap (0 : Fin 2) 1) ∘ A = MS n wstar := by
    apply fin2_ext
    · simp [A, B, MS, w', gx, gy]; group
    · simp [A, B, MS, gx, gy, pow_two]; group
  rwa [e] at h

end MS1
end AC
