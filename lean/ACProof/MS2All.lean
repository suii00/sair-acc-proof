import ACProof.NewFamilies

/-!
# `MS(2, y⁻¹ x y^{1-q} x⁻¹)` is AC-trivial for all `q ∈ ℤ`; hence `MS(2, wA m)` for all `m`.

* `v q = y⁻¹ x y^{1-q} x⁻¹`.
* Shift lemma: in `BS(2,3) = F/⟨⟨x⁻¹y²xy⁻³⟩⟩`, the relator `x v(q+3)⁻¹` is the conjugate by
  `y⁴` of `x v(q)⁻¹`, so `MS(2, v q) ~ MS(2, v (q+3))`.
* Base cases: `q = 0` (`v 0 = w⋆`, Shehper Thm 3), `q = 1` (`v 1 = y⁻¹`),
  `q = -1` (explicit 19-move path, found by greedy search, kernel-checked).
-/

namespace AC
open Function

abbrev v (q : ℤ) : Word 2 := gy⁻¹ * gx * gy ^ (1 - q) * gx⁻¹

section Shift
variable {Q : Type*} [Group Q] {X Y : Q}

theorem shift_identity (hK : Y ^ (2 : ℤ) * X = X * Y ^ (3 : ℤ)) (q : ℤ) :
    X * (Y⁻¹ * X * Y ^ (1 - (q + 3)) * X⁻¹)⁻¹ =
      Y ^ (4 : ℤ) * (X * (Y⁻¹ * X * Y ^ (1 - q) * X⁻¹)⁻¹) * (Y ^ (4 : ℤ))⁻¹ := by
  have h1 : X * Y ^ (3 : ℤ) * X⁻¹ = Y ^ (2 : ℤ) := by
    calc X * Y ^ (3 : ℤ) * X⁻¹ = Y ^ (2 : ℤ) * X * X⁻¹ := by rw [← hK]
      _ = Y ^ (2 : ℤ) := by group
  have h2 : Y ^ (4 : ℤ) * X = X * Y ^ (6 : ℤ) := by
    calc Y ^ (4 : ℤ) * X = Y ^ (2 : ℤ) * (Y ^ (2 : ℤ) * X) := by group
      _ = Y ^ (2 : ℤ) * (X * Y ^ (3 : ℤ)) := by rw [hK]
      _ = (Y ^ (2 : ℤ) * X) * Y ^ (3 : ℤ) := by group
      _ = (X * Y ^ (3 : ℤ)) * Y ^ (3 : ℤ) := by rw [hK]
      _ = X * Y ^ (6 : ℤ) := by group
  have h3 : Y ^ (6 : ℤ) = X * Y ^ (9 : ℤ) * X⁻¹ := by
    calc Y ^ (6 : ℤ) = Y ^ (2 : ℤ) * Y ^ (2 : ℤ) * Y ^ (2 : ℤ) := by group
      _ = (X * Y ^ (3 : ℤ) * X⁻¹) * (X * Y ^ (3 : ℤ) * X⁻¹) * (X * Y ^ (3 : ℤ) * X⁻¹) := by
          rw [h1]
      _ = X * Y ^ (9 : ℤ) * X⁻¹ := by group
  have hc : Y ^ (6 : ℤ) * (X * Y ^ (q - 1) * X⁻¹) = (X * Y ^ (q - 1) * X⁻¹) * Y ^ (6 : ℤ) := by
    rw [h3]; group
  calc X * (Y⁻¹ * X * Y ^ (1 - (q + 3)) * X⁻¹)⁻¹
      = X * (X * Y ^ (q - 1) * X⁻¹) * (X * Y ^ (3 : ℤ) * X⁻¹) * Y := by group
    _ = X * (X * Y ^ (q - 1) * X⁻¹) * Y ^ (2 : ℤ) * Y := by rw [h1]
    _ = X * ((X * Y ^ (q - 1) * X⁻¹) * Y ^ (6 : ℤ)) * Y ^ (-(3 : ℤ)) := by group
    _ = X * (Y ^ (6 : ℤ) * (X * Y ^ (q - 1) * X⁻¹)) * Y ^ (-(3 : ℤ)) := by rw [hc]
    _ = (X * Y ^ (6 : ℤ)) * (X * Y ^ (q - 1) * X⁻¹) * Y ^ (-(3 : ℤ)) := by group
    _ = (Y ^ (4 : ℤ) * X) * (X * Y ^ (q - 1) * X⁻¹) * Y ^ (-(3 : ℤ)) := by rw [h2]
    _ = _ := by group
end Shift

theorem K2 : (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure
      ({gx⁻¹ * gy ^ 2 * gx * (gy ^ (2 + 1))⁻¹} : Set (Word 2))) ^ (2 : ℤ) * QuotientGroup.mk gx =
    QuotientGroup.mk gx * (QuotientGroup.mk gy) ^ (3 : ℤ) := by
  have := K_rel 2
  simpa using this

/-- **Shift.** `MS(2, v q)` reaches `MS(2, v (q+3))`. -/
theorem MS2_v_shift (q : ℤ) : Reachable (MS 2 (v q)) (MS 2 (v (q + 3))) := by
  have s1 := reach_slot1_conj (MS 2 (v q) 0) (gx * (v q)⁻¹) (gy ^ (4 : ℤ))
  refine s1.trans' (reach_slot1_mod _ _ _ ?_)
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  exact (shift_identity K2 q).symm

theorem MS2_v_equiv_add (q : ℤ) (t : ℕ) : Reachable (MS 2 (v q)) (MS 2 (v (q + 3 * t))) := by
  induction t with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ t ih =>
    have := MS2_v_shift (q + 3 * t)
    have e : q + 3 * ((t + 1 : ℕ) : ℤ) = q + 3 * t + 3 := by push_cast; ring
    rw [e]; exact ih.trans' this

theorem MS2_v_equiv (q t : ℤ) : Reachable (MS 2 (v q)) (MS 2 (v (q + 3 * t))) := by
  rcases Int.eq_nat_or_neg t with ⟨k, rfl | rfl⟩
  · exact MS2_v_equiv_add q k
  · have := MS2_v_equiv_add (q + 3 * -(k : ℤ)) k
    have e : q + 3 * -(k : ℤ) + 3 * k = q := by ring
    rw [e] at this; exact this.symm

theorem MS2_vm1_path : Reachable ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹), (gy)] := by
  have s0 : Reachable ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 0 gx) (by apply fin2_ext <;> step_tac)
  have s1 : Reachable ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac)
  have s2 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac)
  have s3 : Reachable ![(gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac)
  have s4 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s5 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s6 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  have s7 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx * gy)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx * gy)] 0 gy) (by apply fin2_ext <;> step_tac)
  have s8 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx * gy)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s9 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gx * gy * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gx)] 1 gy) (by apply fin2_ext <;> step_tac)
  have s10 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gx * gy * gx * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gx * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gx * gy * gx * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  have s11 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gx * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy⁻¹ * gx * gx * gx)] 1 gx) (by apply fin2_ext <;> step_tac)
  have s12 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  have s13 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gx * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gx * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gx * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac)
  have s14 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gx * gy⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gx * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac)
  have s15 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹)] ![(gx⁻¹), (gx * gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac)
  have s16 : Reachable ![(gx⁻¹), (gx * gx * gy⁻¹)] ![(gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹), (gx * gx * gy⁻¹)] 1) (by apply fin2_ext <;> step_tac)
  have s17 : Reachable ![(gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  have s18 : Reachable ![(gx⁻¹), (gy * gx⁻¹)] ![(gx⁻¹), (gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  exact s0.trans' (s1.trans' (s2.trans' (s3.trans' (s4.trans' (s5.trans' (s6.trans' (s7.trans' (s8.trans' (s9.trans' (s10.trans' (s11.trans' (s12.trans' (s13.trans' (s14.trans' (s15.trans' (s16.trans' (s17.trans' (s18))))))))))))))))))

theorem MS2_v_base0 : Reachable (MS 2 (v 0)) (standard 2) := by
  have e : v 0 = wstar := by simp only [v, wstar]; group
  rw [e]; exact MS_wstar_reachable 2

theorem MS2_v_base1 : Reachable (MS 2 (v 1)) (standard 2) := by
  have e : v 1 = gy ^ (-1 : ℤ) := by simp only [v]; group
  rw [e]; exact MS_ypow_reachable 2 (-1)

theorem MS2_v_basem1 : Reachable (MS 2 (v (-1))) (standard 2) := by
  have e0 : MS 2 (v (-1)) = ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹),
      (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := by
    refine fin2_ext ?_ ?_
    · simp [MS, pow_succ, mul_assoc]
    · simp only [MS, v, Matrix.cons_val_one, Matrix.cons_val_zero]; group
  rw [e0]
  refine MS2_vm1_path.trans' ?_
  have t := reach_inv ![gx⁻¹, gy] 0
  exact reach_of_eq t (by apply fin2_ext <;> simp [standard])

/-- **Theorem.** `MS(2, y⁻¹ x y^{1-q} x⁻¹)` is AC-trivial for every `q ∈ ℤ`. -/
theorem MS2_v_reachable (q : ℤ) : Reachable (MS 2 (v q)) (standard 2) := by
  have hr : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  have base : Reachable (MS 2 (v (q % 3))) (standard 2) := by
    rcases hr with h | h | h
    · rw [h]; exact MS2_v_base0
    · rw [h]; exact MS2_v_base1
    · rw [h]
      have := MS2_v_equiv (-1) 1
      norm_num at this
      exact this.symm.trans' MS2_v_basem1
  have := MS2_v_equiv (q % 3) (-(q / 3))
  rw [show q % 3 + 3 * -(q / 3) = q % 3 - 3 * (q / 3) by ring] at this
  have h2 : Reachable (MS 2 (v q)) (MS 2 (v (q % 3))) := by
    have := MS2_v_equiv q (-(q / 3))
    rwa [show q + 3 * -(q / 3) = q % 3 by omega] at this
  exact h2.trans' base

/-- **Corollary.** `MS(2, y^{-m} x y^m x⁻¹)` is AC-trivial for every `m ∈ ℤ`. -/
theorem MS2_wA_all (m : ℤ) : Reachable (MS 2 (wA m)) (standard 2) := by
  have hm : m = (m / 2) * (2 : ℕ) + m % 2 := by push_cast; omega
  have hr : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hr with h | h
  · have := MS_wA_mult 2 (m / 2)
    rwa [show (m / 2) * ((2 : ℕ) : ℤ) = m by push_cast; omega] at this
  · have h1 := MS_wA_reduce 2 (m / 2) 1
    rw [show (m / 2) * ((2 : ℕ) : ℤ) + 1 = m by push_cast; omega] at h1
    exact h1.trans' (MS2_v_reachable (m / 2))

end AC
