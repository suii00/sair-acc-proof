import ACProof.N3

/-!
# `MS(3, wA 5)` is AC-trivial **iff** `AK(3)` is AC-trivial.

Ingredients:
* `phiK k : x ↦ x yᵏ, y ↦ y` is an automorphism of `F(x,y)` (inverse `phiK (-k)`). It sends the first Miller–Schupp
  relator to a conjugate of itself, so it transports AC-reachability (`Reachable.map`).
* In `BS(3,4)`: `y³ x y⁻⁵ x⁻¹ y⁵ x = x y⁻¹ x⁻¹ y⁻¹ x y⁸`, i.e. `x⁻¹ · phiK 3 (x·wA(5)⁻¹) · x = x · w₈⁻¹`.
* `MS(3, w₈) ~ MS(3, w₁) ~ AK(3)` (`MS_wk_equiv`, `AK_reach_MS`; [SMF] Thm 6, [MMS] Prop 1.3).

This is a transfer of AC-triviality in both directions (no AC path between `MS(3, wA 5)` and `AK(3)` is constructed).
-/

namespace AC

/-- `x ↦ x yᵏ`, `y ↦ y`. -/
def phiK (k : ℤ) : Word 2 →* Word 2 := FreeGroup.lift ![gx * gy ^ k, gy]

@[simp] lemma phiK_gx (k : ℤ) : phiK k gx = gx * gy ^ k := by simp [phiK]
@[simp] lemma phiK_gy (k : ℤ) : phiK k gy = gy := by simp [phiK]

lemma phiK_inv_comp (k : ℤ) (w : Word 2) : phiK (-k) (phiK k w) = w := by
  have : (phiK (-k)).comp (phiK k) = MonoidHom.id _ := by
    ext i; fin_cases i <;> simp [phiK, zpow_neg]
  exact DFunLike.congr_fun this w

/-- `![x yᵏ, y]` is AC-trivial. -/
lemma std_of_xyk (k : ℤ) : Reachable ![gx * gy ^ k, gy] (standard 2) := by
  have h : Reachable ![gx * gy ^ k, gy] ![gx, gy] := by
    refine reach_slot0_mod _ _ _ ?_
    have hy : (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure ({gy} : Set (Word 2))) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hy]
  refine h.trans' ?_
  exact std_xy (Or.inl rfl) (Or.inl rfl)

section Link
variable {Q : Type*} [Group Q] {X Y : Q}
lemma link_identity (hK : Y ^ (3 : ℤ) * X = X * Y ^ (4 : ℤ)) :
    Y ^ (3 : ℤ) * X * Y ^ (-5 : ℤ) * X⁻¹ * Y ^ (5 : ℤ) * X = X * Y⁻¹ * X⁻¹ * Y⁻¹ * X * Y ^ (8 : ℤ) := by
  have h6 : Y ^ (6 : ℤ) * X = X * Y ^ (8 : ℤ) := by
    calc Y ^ (6 : ℤ) * X = Y ^ (3 : ℤ) * (Y ^ (3 : ℤ) * X) := by group
      _ = Y ^ (3 : ℤ) * (X * Y ^ (4 : ℤ)) := by rw [hK]
      _ = (Y ^ (3 : ℤ) * X) * Y ^ (4 : ℤ) := by group
      _ = X * Y ^ (4 : ℤ) * Y ^ (4 : ℤ) := by rw [hK]
      _ = X * Y ^ (8 : ℤ) := by group
  calc Y ^ (3 : ℤ) * X * Y ^ (-5 : ℤ) * X⁻¹ * Y ^ (5 : ℤ) * X
      = X * Y ^ (4 : ℤ) * Y ^ (-5 : ℤ) * X⁻¹ * Y ^ (5 : ℤ) * X := by rw [hK]
    _ = X * Y⁻¹ * X⁻¹ * Y⁻¹ * (Y ^ (6 : ℤ) * X) := by group
    _ = _ := by rw [h6]; group
end Link

/-- `phiK 3 ∘ MS(3, wA 5)` is AC-equivalent to `MS(3, w₈)`. -/
theorem phi_MS3_wA5_reach_wk8 : Reachable (phiK 3 ∘ MS 3 (wA 5)) (MS 3 (wk 8)) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ 3 * gx * (gy ^ (3 + 1))⁻¹
  have e : phiK 3 ∘ MS 3 (wA 5) = ![phiK 3 r0, phiK 3 (gx * (wA 5)⁻¹)] := by
    apply fin2_ext <;> rfl
  rw [e]
  -- slot 0: conjugate by y³ to get back r0
  have s0 := reach_slot0_conj (phiK 3 r0) (phiK 3 (gx * (wA 5)⁻¹)) (gy ^ (3 : ℤ))
  have e0 : gy ^ (3 : ℤ) * phiK 3 r0 * (gy ^ (3 : ℤ))⁻¹ = r0 := by
    simp only [r0, map_mul, map_inv, map_pow, phiK_gx, phiK_gy]; group
  rw [e0] at s0
  refine s0.trans' ?_
  -- slot 1: conjugate by x⁻¹, then equality modulo r0
  have s1 := reach_slot1_conj r0 (phiK 3 (gx * (wA 5)⁻¹)) gx⁻¹
  refine s1.trans' ?_
  have hMS : MS 3 (wk 8) = ![r0, gx * (wk 8)⁻¹] := rfl
  rw [hMS]
  refine reach_slot1_mod _ _ _ ?_
  have K : (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure ({r0} : Set (Word 2))) ^ ((3 : ℕ) : ℤ) *
      QuotientGroup.mk gx = QuotientGroup.mk gx * (QuotientGroup.mk gy) ^ (((3 : ℕ) : ℤ) + 1) := K_rel 3
  simp only [wA, wk, map_mul, map_inv, map_zpow, phiK_gx, phiK_gy, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_zpow] at K ⊢
  push_cast at K
  have L := link_identity K
  rw [← mul_inv_eq_one]
  have L2 := mul_inv_eq_one.mpr L
  convert L2 using 1
  group

lemma phiK_comp_MS (k : ℤ) (R : Relators 2) : phiK (-k) ∘ (phiK k ∘ R) = R := by
  funext i; simp [phiK_inv_comp]

lemma phiK_std (k : ℤ) : phiK k ∘ standard 2 = ![gx * gy ^ k, gy] := by
  apply fin2_ext <;> simp [standard]

/-- **`MS(3, wA 5)` is AC-trivial iff `AK(3)` is AC-trivial.** -/
theorem MS3_wA5_iff_AK3 :
    Reachable (MS 3 (wA 5)) (standard 2) ↔ Reachable (AK 3) (standard 2) := by
  have A := phi_MS3_wA5_reach_wk8
  have B : Reachable (AK 3) (MS 3 (wk 8)) := (AK_reach_MS 3).trans' (MS_wk_equiv 3 1 8)
  constructor
  · intro h
    have h1 := h.map (phiK 3)
    rw [phiK_std] at h1
    exact B.trans' (A.symm.trans' (h1.trans' (std_of_xyk 3)))
  · intro h
    have h1 : Reachable (phiK 3 ∘ MS 3 (wA 5)) (standard 2) := A.trans' (B.symm.trans' h)
    have h2 := h1.map (phiK (-3))
    rw [phiK_comp_MS, phiK_std] at h2
    exact h2.trans' (std_of_xyk (-3))

/-- Hence every open class `m ≡ ±5 (mod 12)` for `n = 3` is AC-triviality-equivalent to `AK(3)`
(direction used here: `AK(3)` AC-trivial ⇒ `MS(3, wA m)` AC-trivial for every `m`). -/
theorem MS3_wA_of_AK3 (hAK : Reachable (AK 3) (standard 2)) (m : ℤ) :
    Reachable (MS 3 (wA m)) (standard 2) := by
  have h5 := MS3_wA5_iff_AK3.mpr hAK
  have per : ∀ r : ℤ, Reachable (MS 3 (wA r)) (standard 2) → ∀ t : ℤ,
      Reachable (MS 3 (wA (r + t * 12))) (standard 2) := fun r hr t => by
    have := (MS_wA_period_mul 3 r t).symm
    rw [show r + t * ((((3 : ℕ) : ℤ) + 1) * ((3 : ℕ) : ℤ)) = r + t * 12 by push_cast; ring] at this
    exact this.trans' hr
  by_cases hm5 : m % 12 = 5
  · have := per 5 h5 (m / 12)
    rwa [show 5 + m / 12 * 12 = m by have := Int.emod_add_mul_ediv m 12; linarith] at this
  by_cases hm7 : m % 12 = 7
  · have h7 : Reachable (MS 3 (wA 7)) (standard 2) := by
      apply MS_wA_negate
      have := per 5 h5 (-1)
      rwa [show (5 : ℤ) + -1 * 12 = -7 by norm_num] at this
    have := per 7 h7 (m / 12)
    rwa [show 7 + m / 12 * 12 = m by have := Int.emod_add_mul_ediv m 12; linarith] at this
  exact MS3_wA m hm5 hm7

end AC
