import ACProof.AK3Link
import ACProof.N4

/-!
# `MS(4, wA (-9))` is AC-trivial **iff** `AK(4)` is AC-trivial.

Same mechanism as `AK3Link`: the automorphism `phiK (-6) : x ↦ x y⁻⁶` and, in `BS(4,5)`,
`g · (x y⁻⁶ x y⁹ x⁻¹ y⁻⁹) · g⁻¹ = x · w₋₉⁻¹` with `g = y⁻¹ x⁻¹ y⁻⁴`.
Consequence: `AK(4)` AC-trivial ⇒ `MS(4, wA m)` AC-trivial for all `m ≡ ±9 (mod 20)`.
-/

namespace AC

section Link4
variable {Q : Type*} [Group Q] {X Y : Q}

lemma bs_pow (a b : ℤ) (hK : Y ^ a * X = X * Y ^ b) (k : ℤ) : Y ^ (a * k) * X = X * Y ^ (b * k) := by
  have hc : X⁻¹ * Y ^ a * X = Y ^ b := by rw [mul_assoc, hK]; group
  have e : (X⁻¹ * Y ^ a * X⁻¹⁻¹) ^ k = X⁻¹ * (Y ^ a) ^ k * X⁻¹⁻¹ := conj_zpow
  rw [inv_inv, hc] at e
  calc Y ^ (a * k) * X = X * (X⁻¹ * (Y ^ a) ^ k * X) := by rw [← zpow_mul]; group
    _ = X * Y ^ (b * k) := by rw [← e, ← zpow_mul]

lemma link4_identity (hK : Y ^ (4 : ℤ) * X = X * Y ^ (5 : ℤ)) :
    Y⁻¹ * X⁻¹ * Y ^ (-4 : ℤ) * (X * Y ^ (-6 : ℤ) * X * Y ^ (9 : ℤ) * X⁻¹ * Y ^ (-9 : ℤ)) *
      (Y⁻¹ * X⁻¹ * Y ^ (-4 : ℤ))⁻¹ = X * Y⁻¹ * X⁻¹ * Y⁻¹ * X * Y ^ (-9 : ℤ) := by
  have p1 := bs_pow 4 5 hK (-1)
  rw [show (4 : ℤ) * (-1) = -4 by norm_num, show (5 : ℤ) * (-1) = -5 by norm_num] at p1
  have p2 := bs_pow 4 5 hK (-3)
  rw [show (4 : ℤ) * (-3) = -12 by norm_num, show (5 : ℤ) * (-3) = -15 by norm_num] at p2
  have p3 := bs_pow 4 5 hK (-2)
  rw [show (4 : ℤ) * (-2) = -8 by norm_num, show (5 : ℤ) * (-2) = -10 by norm_num] at p3
  have h1 : X⁻¹ * Y ^ (-4 : ℤ) * X = Y ^ (-5 : ℤ) := by rw [mul_assoc, p1]; group
  calc Y⁻¹ * X⁻¹ * Y ^ (-4 : ℤ) * (X * Y ^ (-6 : ℤ) * X * Y ^ (9 : ℤ) * X⁻¹ * Y ^ (-9 : ℤ)) *
        (Y⁻¹ * X⁻¹ * Y ^ (-4 : ℤ))⁻¹
      = Y⁻¹ * (X⁻¹ * Y ^ (-4 : ℤ) * X) * Y ^ (-6 : ℤ) * X * Y ^ (9 : ℤ) * X⁻¹ * Y ^ (-5 : ℤ) * X * Y := by
        group
    _ = (Y ^ (-12 : ℤ) * X) * Y ^ (9 : ℤ) * X⁻¹ * Y ^ (-5 : ℤ) * X * Y := by rw [h1]; group
    _ = X * Y ^ (-15 : ℤ) * Y ^ (9 : ℤ) * X⁻¹ * Y ^ (-5 : ℤ) * X * Y := by rw [p2]
    _ = X * Y⁻¹ * (X * Y ^ (5 : ℤ))⁻¹ * Y ^ (-5 : ℤ) * X * Y := by group
    _ = X * Y⁻¹ * (Y ^ (4 : ℤ) * X)⁻¹ * Y ^ (-5 : ℤ) * X * Y := by rw [← hK]
    _ = X * Y⁻¹ * X⁻¹ * Y⁻¹ * (Y ^ (-8 : ℤ) * X) * Y := by group
    _ = X * Y⁻¹ * X⁻¹ * Y⁻¹ * (X * Y ^ (-10 : ℤ)) * Y := by rw [p3]
    _ = X * Y⁻¹ * X⁻¹ * Y⁻¹ * X * Y ^ (-9 : ℤ) := by group
end Link4

theorem phi_MS4_wAm9_reach_wkm9 : Reachable (phiK (-6) ∘ MS 4 (wA (-9))) (MS 4 (wk (-9))) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ 4 * gx * (gy ^ (4 + 1))⁻¹
  have e : phiK (-6) ∘ MS 4 (wA (-9)) = ![phiK (-6) r0, phiK (-6) (gx * (wA (-9))⁻¹)] := by
    apply fin2_ext <;> rfl
  rw [e]
  have s0 := reach_slot0_conj (phiK (-6) r0) (phiK (-6) (gx * (wA (-9))⁻¹)) (gy ^ (-6 : ℤ))
  have e0 : gy ^ (-6 : ℤ) * phiK (-6) r0 * (gy ^ (-6 : ℤ))⁻¹ = r0 := by
    simp only [r0, map_mul, map_inv, map_pow, phiK_gx, phiK_gy]; group
  rw [e0] at s0
  refine s0.trans' ?_
  have s1 := reach_slot1_conj r0 (phiK (-6) (gx * (wA (-9))⁻¹)) (gy⁻¹ * gx⁻¹ * gy ^ (-4 : ℤ))
  refine s1.trans' ?_
  have hMS : MS 4 (wk (-9)) = ![r0, gx * (wk (-9))⁻¹] := rfl
  rw [hMS]
  refine reach_slot1_mod _ _ _ ?_
  have K : (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure ({r0} : Set (Word 2))) ^ ((4 : ℕ) : ℤ) *
      QuotientGroup.mk gx = QuotientGroup.mk gx * (QuotientGroup.mk gy) ^ (((4 : ℕ) : ℤ) + 1) := K_rel 4
  simp only [wA, wk, map_mul, map_inv, map_zpow, phiK_gx, phiK_gy, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_zpow] at K ⊢
  push_cast at K
  have L := link4_identity K
  rw [← mul_inv_eq_one]
  have L2 := mul_inv_eq_one.mpr L
  convert L2 using 1
  group

/-- **`MS(4, wA (-9))` is AC-trivial iff `AK(4)` is AC-trivial.** -/
theorem MS4_wAm9_iff_AK4 :
    Reachable (MS 4 (wA (-9))) (standard 2) ↔ Reachable (AK 4) (standard 2) := by
  have A := phi_MS4_wAm9_reach_wkm9
  have B : Reachable (AK 4) (MS 4 (wk (-9))) := (AK_reach_MS 4).trans' (MS_wk_equiv 4 1 (-9))
  constructor
  · intro h
    have h1 := h.map (phiK (-6))
    rw [phiK_std] at h1
    exact B.trans' (A.symm.trans' (h1.trans' (std_of_xyk (-6))))
  · intro h
    have h1 : Reachable (phiK (-6) ∘ MS 4 (wA (-9))) (standard 2) := A.trans' (B.symm.trans' h)
    have h2 := h1.map (phiK (-(-6)))
    rw [phiK_comp_MS, phiK_std] at h2
    exact h2.trans' (std_of_xyk _)

/-- If `AK(4)` is AC-trivial, then `MS(4, wA m)` is AC-trivial for every `m ≡ ±9 (mod 20)`. -/
theorem MS4_wA_9_11_of_AK4 (hAK : Reachable (AK 4) (standard 2)) (m : ℤ)
    (hm : m % 20 = 9 ∨ m % 20 = 11) : Reachable (MS 4 (wA m)) (standard 2) := by
  have hm9 := MS4_wAm9_iff_AK4.mpr hAK
  have per : ∀ r : ℤ, Reachable (MS 4 (wA r)) (standard 2) → ∀ t : ℤ,
      Reachable (MS 4 (wA (r + t * 20))) (standard 2) := fun r hr t => by
    have := (MS_wA_period_mul 4 r t).symm
    rw [show r + t * ((((4 : ℕ) : ℤ) + 1) * ((4 : ℕ) : ℤ)) = r + t * 20 by push_cast; ring] at this
    exact this.trans' hr
  have h11 : Reachable (MS 4 (wA 11)) (standard 2) := by
    have := per (-9) hm9 1; norm_num at this; exact this
  have h9 : Reachable (MS 4 (wA 9)) (standard 2) := MS_wA_negate 4 9 (by simpa using hm9)
  rcases hm with h | h
  · have := per 9 h9 (m / 20)
    rwa [show 9 + m / 20 * 20 = m by have := Int.emod_add_mul_ediv m 20; linarith] at this
  · have := per 11 h11 (m / 20)
    rwa [show 11 + m / 20 * 20 = m by have := Int.emod_add_mul_ediv m 20; linarith] at this

end AC
