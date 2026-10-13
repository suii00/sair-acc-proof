import ACProof.MS2

/-!
# Akbulut–Kirby presentations and [MMS02, Prop. 1.3]; Shehper et al. Theorem 7

* `AK n = ![xⁿ y^{-(n+1)}, x y x (y x y)⁻¹]`, i.e. `⟨x,y | xⁿ = y^{n+1}, xyx = yxy⟩`.
* `AK_reach_MS` : `AK(n) ~ MS(n, w₁)` with `w₁ = y⁻¹x⁻¹yxy`
  (Myasnikov–Myasnikov–Shpilrain, Contemp. Math. 296 (2002), Prop. 1.3; = Prop. 5 in
  arXiv:2408.15332v2). Proven for all `n : ℕ` (paper: `n ≥ 2`).
* `AK2_reachable` : AK(2) is AC-trivial (corollary with `MS2_wk_reachable`).
* `MS_reach_P` : `MS(n, w_k) ~ P(n,k)` (Shehper et al. v2, Theorem 7).
-/

namespace AC
open Function

def AK (n : ℕ) : Relators 2 :=
  ![gx ^ n * (gy ^ (n + 1))⁻¹, gx * gy * gx * (gy * gx * gy)⁻¹]

theorem reach_slot0_mod (a a' r : Word 2)
    (h : (QuotientGroup.mk a : Word 2 ⧸ Subgroup.normalClosure ({r} : Set (Word 2))) =
      QuotientGroup.mk a') :
    Reachable ![a, r] ![a', r] := by
  refine reach_of_mul _ _ (i := 0) (j := 1) (by decide) (a⁻¹ * a') ?_ ?_
  · show a⁻¹ * a' ∈ Subgroup.normalClosure {r}
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h,
      inv_mul_cancel]
  · refine fin2_ext ?_ rfl; simp

theorem reach_slot0_conj (a r c : Word 2) : Reachable ![a, r] ![c * a * c⁻¹, r] :=
  reach_of_conj _ _ 0 c (by refine fin2_ext ?_ rfl; simp)

/-- **[MMS02, Prop. 1.3].** `AK(n)` reaches `MS(n, w₁)`. -/
theorem AK_reach_MS (n : ℕ) : Reachable (AK n) (MS n (wk 1)) := by
  set r1 : Word 2 := gx * (wk 1)⁻¹
  -- slot 1: xyx(yxy)⁻¹ ↦ conjugate by (xy)⁻¹ = x(w₁)⁻¹
  have s1 : Reachable (AK n) ![gx ^ n * (gy ^ (n + 1))⁻¹, r1] := by
    have := reach_slot1_conj (gx ^ n * (gy ^ (n + 1))⁻¹) (gx * gy * gx * (gy * gx * gy)⁻¹)
      (gx * gy)⁻¹
    convert this using 1
    refine fin2_ext rfl ?_
    simp only [r1, wk, Matrix.cons_val_one, Matrix.cons_val_zero]; group
  -- slot 0 modulo r1: xⁿ ≡ (xy)⁻¹ yⁿ (xy)
  have s2 : Reachable ![gx ^ n * (gy ^ (n + 1))⁻¹, r1]
      ![(gx * gy)⁻¹ * gy ^ n * (gx * gy) * (gy ^ (n + 1))⁻¹, r1] := by
    apply reach_slot0_mod
    set N := Subgroup.normalClosure ({r1} : Set (Word 2))
    have hr : (QuotientGroup.mk r1 : Word 2 ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
    set X : Word 2 ⧸ N := QuotientGroup.mk gx
    set Y : Word 2 ⧸ N := QuotientGroup.mk gy
    have hx : X = (X * Y)⁻¹ * Y * (X * Y) := by
      simp only [r1, wk, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow] at hr
      have h' : X = Y ^ (-1 : ℤ) * X⁻¹ * Y * X * Y := mul_inv_eq_one.mp hr
      exact h'.trans (by group)
    have hxn : X ^ n = (X * Y)⁻¹ * Y ^ n * (X * Y) := by
      conv_lhs => rw [hx]
      have := conj_pow (a := (X * Y)⁻¹) (b := Y) (i := n)
      simpa using this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
    change X ^ n * (Y ^ (n + 1))⁻¹ = (X * Y)⁻¹ * Y ^ n * (X * Y) * (Y ^ (n + 1))⁻¹
    rw [hxn]
  have s3 : Reachable ![(gx * gy)⁻¹ * gy ^ n * (gx * gy) * (gy ^ (n + 1))⁻¹, r1]
      (MS n (wk 1)) := by
    have := reach_slot0_conj ((gx * gy)⁻¹ * gy ^ n * (gx * gy) * (gy ^ (n + 1))⁻¹) r1 gy
    convert this using 1
    refine fin2_ext ?_ rfl
    simp only [MS, Matrix.cons_val_zero]; group
  exact s1.trans' (s2.trans' s3)

/-- **Corollary.** AK(2) is AC-trivial. -/
theorem AK2_reachable : Reachable (AK 2) (standard 2) :=
  (AK_reach_MS 2).trans' (MS2_wk_reachable 1)

/-- Shehper et al. `P(n,k) = ⟨x,y | y^{n-k-1}x⁻¹yx = xyx⁻¹y^{n-k}, x = w_k⟩`. -/
def P (n : ℕ) (k : ℤ) : Relators 2 :=
  ![gy ^ ((n : ℤ) - k - 1) * gx⁻¹ * gy * gx * (gx * gy * gx⁻¹ * gy ^ ((n : ℤ) - k))⁻¹,
    gx * (wk k)⁻¹]

/-- **Shehper et al. v2, Theorem 7.** `MS(n, w_k)` reaches `P(n, k)`. -/
theorem MS_reach_P (n : ℕ) (k : ℤ) : Reachable (MS n (wk k)) (P n k) := by
  set r1 : Word 2 := gx * (wk k)⁻¹
  set c0 : Word 2 := gy⁻¹ * gx
  set a0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  have s1 : Reachable (MS n (wk k)) ![c0 * a0 * c0⁻¹, r1] := reach_slot0_conj a0 r1 c0
  have s2 : Reachable ![c0 * a0 * c0⁻¹, r1] (P n k) := by
    apply reach_slot0_mod
    set N := Subgroup.normalClosure ({r1} : Set (Word 2))
    have hr : (QuotientGroup.mk r1 : Word 2 ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
    set X : Word 2 ⧸ N := QuotientGroup.mk gx
    set Y : Word 2 ⧸ N := QuotientGroup.mk gy
    have hx : X = Y ^ (-k) * X⁻¹ * Y * X * Y := by
      simp only [r1, wk, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_zpow] at hr
      exact mul_inv_eq_one.mp hr
    have hXYX : X * Y ^ k * X = Y * X * Y := by
      calc X * Y ^ k * X = X * Y ^ k * (Y ^ (-k) * X⁻¹ * Y * X * Y) := by rw [← hx]
        _ = Y * X * Y := by group
    have h1 : Y ^ k * X * Y⁻¹ = X⁻¹ * Y * X := by
      calc Y ^ k * X * Y⁻¹ = X⁻¹ * (X * Y ^ k * X) * Y⁻¹ := by group
        _ = X⁻¹ * Y * X := by rw [hXYX]; group
    have h2 : Y⁻¹ * X * Y ^ k = X * Y * X⁻¹ := by
      calc Y⁻¹ * X * Y ^ k = Y⁻¹ * (X * Y ^ k * X) * X⁻¹ := by group
        _ = X * Y * X⁻¹ := by rw [hXYX]; group
    simp only [c0, a0, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, QuotientGroup.mk_zpow]
    change (Y⁻¹ * X) * (X⁻¹ * Y ^ n * X * (Y ^ (n + 1))⁻¹) * (Y⁻¹ * X)⁻¹ =
      Y ^ ((n : ℤ) - k - 1) * X⁻¹ * Y * X * (X * Y * X⁻¹ * Y ^ ((n : ℤ) - k))⁻¹
    calc (Y⁻¹ * X) * (X⁻¹ * Y ^ n * X * (Y ^ (n + 1))⁻¹) * (Y⁻¹ * X)⁻¹
        = Y ^ ((n : ℤ) - k - 1) * (Y ^ k * X * Y⁻¹) * ((Y⁻¹ * X * Y ^ k) * Y ^ ((n : ℤ) - k))⁻¹
          := by group
      _ = _ := by rw [h1, h2]; group
  exact s1.trans' s2

end AC
