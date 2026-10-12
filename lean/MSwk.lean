import ACProof.MS1

/-!
# Shehper et al. (arXiv:2408.15332v2) Theorem 6:
for fixed `n`, all `MS(n, w_k)`, `w_k = y^{-k} x⁻¹ y x y`, `k ∈ ℤ`, are AC-equivalent.
-/

namespace AC
open Function

/-- `w_k = y^{-k} x⁻¹ y x y` -/
abbrev wk (k : ℤ) : Word 2 := gy ^ (-k) * gx⁻¹ * gy * gx * gy

/-- Second-slot moves modulo the first relator. -/
theorem reach_slot1_mod (r a a' : Word 2)
    (h : (QuotientGroup.mk a : Word 2 ⧸ Subgroup.normalClosure ({r} : Set (Word 2))) =
      QuotientGroup.mk a') :
    Reachable ![r, a] ![r, a'] := by
  refine reach_of_mul _ _ (i := 1) (j := 0) (by decide) (a⁻¹ * a') ?_ ?_
  · show a⁻¹ * a' ∈ Subgroup.normalClosure {r}
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h,
      inv_mul_cancel]
  · refine fin2_ext rfl ?_; simp

theorem reach_slot1_conj (r a c : Word 2) : Reachable ![r, a] ![r, c * a * c⁻¹] :=
  reach_of_conj _ _ 1 c (by refine fin2_ext rfl ?_; simp)

theorem reach_slot1_inv (r a : Word 2) : Reachable ![r, a] ![r, a⁻¹] := by
  have := reach_inv ![r, a] 1
  convert this using 1; refine fin2_ext rfl ?_; simp

/-- **Theorem 6 step.** `MS(n, w_k)` reaches `MS(n, w_{k+1})`. -/
theorem MS_wk_succ (n : ℕ) (k : ℤ) : Reachable (MS n (wk k)) (MS n (wk (k + 1))) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  set N := Subgroup.normalClosure ({r0} : Set (Word 2))
  set X : Word 2 ⧸ N := QuotientGroup.mk gx
  set Y : Word 2 ⧸ N := QuotientGroup.mk gy
  have hr : (QuotientGroup.mk r0 : Word 2 ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
  -- K : Yⁿ X = X Y^{n+1}
  have K : Y ^ (n : ℤ) * X = X * Y ^ ((n : ℤ) + 1) := by
    simp only [r0, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow] at hr
    have h2 := mul_inv_eq_one.mp hr
    have h3 : X⁻¹ * Y ^ (n : ℤ) * X = Y ^ ((n : ℤ) + 1) := by
      simpa [X, Y, ← zpow_natCast] using h2
    rw [← h3]; group
  have e_MS : ∀ j, MS n (wk j) = ![r0, gx * (wk j)⁻¹] := fun j => rfl
  have mk_eq : ∀ a b : Word 2, (QuotientGroup.mk a : Word 2 ⧸ N) = QuotientGroup.mk b →
      Reachable ![r0, a] ![r0, b] := fun a b h => reach_slot1_mod r0 a b h
  -- forms
  set F1 : Word 2 := gy ^ k * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx
  set F2 : Word 2 := gy ^ (k - n) * gx * gy ^ (n : ℤ) * gx⁻¹ * gy⁻¹ * gx
  set F4 : Word 2 := gy ^ (1 - (n : ℤ)) * gx * gy * gx⁻¹ * gy ^ ((n : ℤ) - k) * gx⁻¹
  set F5 : Word 2 := gy ^ ((n : ℤ) - k) * gx⁻¹ * gy ^ (1 - (n : ℤ)) * gx * gy * gx⁻¹
  set F6 : Word 2 := gy ^ (-(k + 1)) * gx⁻¹ * gy * gx * gy * gx⁻¹
  have m1 : Reachable ![r0, gx * (wk k)⁻¹] ![r0, F1] := by
    have := reach_slot1_conj r0 (gx * (wk k)⁻¹) (gy ^ k)
    convert this using 3; simp only [F1, wk]; group
  have m2 : Reachable ![r0, F1] ![r0, F2] := by
    apply mk_eq
    simp only [F1, F2, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    change Y ^ k * X * Y⁻¹ * X⁻¹ * Y⁻¹ * X = Y ^ (k - n) * X * Y ^ (n : ℤ) * X⁻¹ * Y⁻¹ * X
    calc Y ^ k * X * Y⁻¹ * X⁻¹ * Y⁻¹ * X
        = Y ^ (k - n) * (Y ^ (n : ℤ) * X) * Y⁻¹ * X⁻¹ * Y⁻¹ * X := by group
      _ = Y ^ (k - n) * (X * Y ^ ((n : ℤ) + 1)) * Y⁻¹ * X⁻¹ * Y⁻¹ * X := by rw [K]
      _ = _ := by group
  -- F3 = x F2⁻¹ x⁻¹
  have m3 : Reachable ![r0, F2] ![r0, gx * F2⁻¹ * gx⁻¹] :=
    (reach_slot1_inv r0 F2).trans' (reach_slot1_conj r0 F2⁻¹ gx)
  have m4 : Reachable ![r0, gx * F2⁻¹ * gx⁻¹] ![r0, F4] := by
    apply mk_eq
    simp only [F2, F4, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    change X * (Y ^ (k - n) * X * Y ^ (n : ℤ) * X⁻¹ * Y⁻¹ * X)⁻¹ * X⁻¹ =
      Y ^ (1 - (n : ℤ)) * X * Y * X⁻¹ * Y ^ ((n : ℤ) - k) * X⁻¹
    calc X * (Y ^ (k - n) * X * Y ^ (n : ℤ) * X⁻¹ * Y⁻¹ * X)⁻¹ * X⁻¹
        = Y ^ (1 - (n : ℤ)) * (Y ^ (n : ℤ) * X) * Y ^ (-(n : ℤ)) * X⁻¹ * Y ^ ((n : ℤ) - k)
            * X⁻¹ := by group
      _ = Y ^ (1 - (n : ℤ)) * (X * Y ^ ((n : ℤ) + 1)) * Y ^ (-(n : ℤ)) * X⁻¹
            * Y ^ ((n : ℤ) - k) * X⁻¹ := by rw [K]
      _ = _ := by group
  have m5 : Reachable ![r0, F4] ![r0, F5] := by
    have := reach_slot1_conj r0 F4 (gy ^ ((n : ℤ) - k) * gx⁻¹)
    convert this using 3; simp only [F4, F5]; group
  have m6 : Reachable ![r0, F5] ![r0, F6] := by
    apply mk_eq
    simp only [F5, F6, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    change Y ^ ((n : ℤ) - k) * X⁻¹ * Y ^ (1 - (n : ℤ)) * X * Y * X⁻¹ =
      Y ^ (-(k + 1)) * X⁻¹ * Y * X * Y * X⁻¹
    calc Y ^ ((n : ℤ) - k) * X⁻¹ * Y ^ (1 - (n : ℤ)) * X * Y * X⁻¹
        = Y ^ (-(k + 1)) * X⁻¹ * (X * Y ^ ((n : ℤ) + 1)) * X⁻¹ * Y ^ (1 - (n : ℤ)) * X * Y
            * X⁻¹ := by group
      _ = Y ^ (-(k + 1)) * X⁻¹ * (Y ^ (n : ℤ) * X) * X⁻¹ * Y ^ (1 - (n : ℤ)) * X * Y
            * X⁻¹ := by rw [K]
      _ = _ := by group
  have m7 : Reachable ![r0, F6] ![r0, gx * (wk (k + 1))⁻¹] := by
    have := reach_slot1_inv r0 F6
    convert this using 3; simp only [F6, wk]; group
  rw [e_MS, e_MS]
  exact m1.trans' (m2.trans' (m3.trans' (m4.trans' (m5.trans' (m6.trans' m7)))))

/-- **Theorem 6.** For fixed `n`, all `MS(n, w_k)` are AC-equivalent. -/
theorem MS_wk_equiv (n : ℕ) (k k' : ℤ) : Reachable (MS n (wk k)) (MS n (wk k')) := by
  have up : ∀ (k : ℤ) (m : ℕ), Reachable (MS n (wk k)) (MS n (wk (k + m))) := by
    intro k m
    induction m with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ m ih =>
      have := MS_wk_succ n (k + m)
      push_cast; rw [← add_assoc]; exact ih.trans' this
  rcases le_total k k' with h | h
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
    have := up k m; rwa [← hm, add_sub_cancel] at this
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h)
    have := up k' m; rw [← hm, add_sub_cancel] at this; exact this.symm

/-- Hence AC-triviality of one member gives it for the whole family (fixed `n`). -/
theorem MS_wk_all_of_one (n : ℕ) (k₀ : ℤ) (h : Reachable (MS n (wk k₀)) (standard 2))
    (k : ℤ) : Reachable (MS n (wk k)) (standard 2) :=
  (MS_wk_equiv n k k₀).trans' h

end AC
