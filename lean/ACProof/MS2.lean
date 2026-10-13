import ACProof.MSwk

/-!
# Shehper et al. Corollary 9 / Theorem B(iii): `MS(2, w_k)` is AC-trivial for all `k ∈ ℤ`.

Instead of going through AK(2) and [MMS02, Prop. 5], we use an explicit 21-move
AC path for `MS(2, w_3)` (found by our own greedy search, `/workspace/acc-proof/search`),
kernel-checked move by move, plus Theorem 6 (`MS_wk_equiv`).
-/

namespace AC
open Function

theorem reach_of_eq {n : ℕ} {R S T : Relators n} (h : Reachable R S) (e : S = T) :
    Reachable R T := e ▸ h

macro "step_tac" : tactic =>
  `(tactic| first | rfl | (simp; done) | (simp; group) | group)

theorem MS2_w3_path : Reachable ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] ![(gx⁻¹), (gy⁻¹)] := by
  have s0 : Reachable ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac)
  have s1 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac)
  have s2 : Reachable ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac)
  have s3 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  have s4 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] 0 gx) (by apply fin2_ext <;> step_tac)
  have s5 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] 0 gy) (by apply fin2_ext <;> step_tac)
  have s6 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac)
  have s7 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac)
  have s8 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac)
  have s9 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s10 : Reachable ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s11 : Reachable ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac)
  have s12 : Reachable ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s13 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac)
  have s14 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac)
  have s15 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s16 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  have s17 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac)
  have s18 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac)
  have s19 : Reachable ![(gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  have s20 : Reachable ![(gx⁻¹), (gy⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac)
  exact s0.trans' (s1.trans' (s2.trans' (s3.trans' (s4.trans' (s5.trans' (s6.trans' (s7.trans' (s8.trans' (s9.trans' (s10.trans' (s11.trans' (s12.trans' (s13.trans' (s14.trans' (s15.trans' (s16.trans' (s17.trans' (s18.trans' (s19.trans' (s20))))))))))))))))))))
-- endpoint ((-1,), (-2,))

theorem MS2_w3_reachable : Reachable (MS 2 (wk 3)) (standard 2) := by
  have e0 : MS 2 (wk 3) = ![(gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹),
      (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy)] := by
    refine fin2_ext ?_ ?_
    · simp [MS, pow_succ, mul_assoc]
    · simp [MS, pow_succ, mul_assoc, zpow_ofNat]
  rw [e0]
  refine MS2_w3_path.trans' ?_
  have t1 := reach_inv ![gx⁻¹, gy⁻¹] 0
  have t2 := reach_inv (update ![gx⁻¹, gy⁻¹] 0 (![gx⁻¹, gy⁻¹] 0)⁻¹) 1
  refine t1.trans' (reach_of_eq t2 ?_)
  apply fin2_ext <;> simp [standard]

/-- **Theorem B(iii).** `MS(2, y^{-k} x⁻¹ y x y)` is AC-trivial for every `k ∈ ℤ`. -/
theorem MS2_wk_reachable (k : ℤ) : Reachable (MS 2 (wk k)) (standard 2) :=
  MS_wk_all_of_one 2 3 MS2_w3_reachable k

end AC
