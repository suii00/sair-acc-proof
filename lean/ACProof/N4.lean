import ACProof.General

/-! # `MS(4, wA m)`: certified search paths for residues 2, 6, 14, 18, 19 (mod 20). -/

set_option maxHeartbeats 1000000

namespace AC

theorem n4m2_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s1 : Reachable ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s2 : Reachable ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s3 : Reachable ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s4 : Reachable ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s5 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s6 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s7 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s8 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s9 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s10 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s11 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s12 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s13 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s14 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s15 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s16 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s17 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s18 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s19 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s20 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s21 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s22 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s23 : Reachable ![(gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_s24 : Reachable ![(gx⁻¹), (gy⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m2_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (standard 2) := by
  have fin : Reachable ![(gx⁻¹), (gy⁻¹)] (standard 2) := by std_fin
  exact n4m2_s0.trans' (n4m2_s1.trans' (n4m2_s2.trans' (n4m2_s3.trans' (n4m2_s4.trans' (n4m2_s5.trans' (n4m2_s6.trans' (n4m2_s7.trans' (n4m2_s8.trans' (n4m2_s9.trans' (n4m2_s10.trans' (n4m2_s11.trans' (n4m2_s12.trans' (n4m2_s13.trans' (n4m2_s14.trans' (n4m2_s15.trans' (n4m2_s16.trans' (n4m2_s17.trans' (n4m2_s18.trans' (n4m2_s19.trans' (n4m2_s20.trans' (n4m2_s21.trans' (n4m2_s22.trans' (n4m2_s23.trans' (n4m2_s24.trans' (fin)))))))))))))))))))))))))

theorem MS4_wA_m2 : Reachable (MS 4 (wA (2))) (standard 2) := by
  have h := MS_wA_reduce 4 (0) (2)
  rw [show (0 : ℤ) * ((4 : ℕ) : ℤ) + (2) = 2 by norm_num] at h
  have e : MS 4 (gy ^ (-(2 : ℤ)) * gx * gy ^ ((2 : ℤ) - (0)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n4m2_path

theorem n4m6_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s1 : Reachable ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s2 : Reachable ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s3 : Reachable ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s4 : Reachable ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s5 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s6 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s7 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s8 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s9 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s10 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy * gy * gy * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy⁻¹ * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s11 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy * gy * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx * gx * gy * gy * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy * gy * gy * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s12 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx * gx * gy * gy * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gy * gx * gx * gy * gy * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx * gx * gy * gy * gy * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s13 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gy * gx * gx * gy * gy * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx * gx * gy * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gy * gx * gx * gy * gy * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s14 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx * gx * gy * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx * gx * gy * gy * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s15 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s16 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s17 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s18 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s19 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s20 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s21 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx * gy * gx⁻¹ * gy⁻¹)] 1) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s22 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s23 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s24 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s25 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s26 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s27 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s28 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s29 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s30 : Reachable ![(gx * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s31 : Reachable ![(gx * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gx⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s32 : Reachable ![(gx * gy * gx⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx * gy * gx⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s33 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s34 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s35 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s36 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s37 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s38 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s39 : Reachable ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s40 : Reachable ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx * gy)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx * gy)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s41 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx * gy)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s42 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s43 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s44 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s45 : Reachable ![(gx⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gx), (gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s46 : Reachable ![(gy * gx), (gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gx), (gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s47 : Reachable ![(gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹), (gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_s48 : Reachable ![(gy⁻¹), (gx⁻¹ * gy⁻¹)] ![(gy⁻¹), (gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹), (gx⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m6_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] (standard 2) := by
  have fin : Reachable ![(gy⁻¹), (gx⁻¹)] (standard 2) := by std_fin
  exact n4m6_s0.trans' (n4m6_s1.trans' (n4m6_s2.trans' (n4m6_s3.trans' (n4m6_s4.trans' (n4m6_s5.trans' (n4m6_s6.trans' (n4m6_s7.trans' (n4m6_s8.trans' (n4m6_s9.trans' (n4m6_s10.trans' (n4m6_s11.trans' (n4m6_s12.trans' (n4m6_s13.trans' (n4m6_s14.trans' (n4m6_s15.trans' (n4m6_s16.trans' (n4m6_s17.trans' (n4m6_s18.trans' (n4m6_s19.trans' (n4m6_s20.trans' (n4m6_s21.trans' (n4m6_s22.trans' (n4m6_s23.trans' (n4m6_s24.trans' (n4m6_s25.trans' (n4m6_s26.trans' (n4m6_s27.trans' (n4m6_s28.trans' (n4m6_s29.trans' (n4m6_s30.trans' (n4m6_s31.trans' (n4m6_s32.trans' (n4m6_s33.trans' (n4m6_s34.trans' (n4m6_s35.trans' (n4m6_s36.trans' (n4m6_s37.trans' (n4m6_s38.trans' (n4m6_s39.trans' (n4m6_s40.trans' (n4m6_s41.trans' (n4m6_s42.trans' (n4m6_s43.trans' (n4m6_s44.trans' (n4m6_s45.trans' (n4m6_s46.trans' (n4m6_s47.trans' (n4m6_s48.trans' (fin)))))))))))))))))))))))))))))))))))))))))))))))))

theorem MS4_wA_m6 : Reachable (MS 4 (wA (6))) (standard 2) := by
  have h := MS_wA_reduce 4 (1) (2)
  rw [show (1 : ℤ) * ((4 : ℕ) : ℤ) + (2) = 6 by norm_num] at h
  have e : MS 4 (gy ^ (-(2 : ℤ)) * gx * gy ^ ((2 : ℤ) - (1)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gx⁻¹ * gy * gy)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n4m6_path

theorem n4m14_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s1 : Reachable ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s2 : Reachable ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s3 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s4 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s5 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s6 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s7 : Reachable ![(gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s8 : Reachable ![(gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s9 : Reachable ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s10 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s11 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s12 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s13 : Reachable ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s14 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s15 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s16 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s17 : Reachable ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s18 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s19 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s20 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s21 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s22 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gy * gx⁻¹ * gy * gx⁻¹)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy)] 1) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s23 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gy * gx⁻¹ * gy * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gy * gx⁻¹ * gy * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s24 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s25 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s26 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gx⁻¹ * gy * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s27 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gx⁻¹ * gy * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gy * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s28 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gx⁻¹ * gy * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s29 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s30 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s31 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s32 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s33 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_inv ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s34 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy * gy * gy)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy * gy)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s35 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy * gy * gy)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy * gy * gy)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s36 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s37 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s38 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s39 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s40 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s41 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s42 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s43 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gy * gy)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s44 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gy * gy)] ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gy * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s45 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gx⁻¹ * gy * gy), (gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s46 : Reachable ![(gx⁻¹ * gy), (gx⁻¹ * gy * gy)] ![(gy⁻¹ * gx), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy), (gx⁻¹ * gy * gy)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s47 : Reachable ![(gy⁻¹ * gx), (gx⁻¹ * gy * gy)] ![(gy), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx), (gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s48 : Reachable ![(gy), (gx⁻¹ * gy * gy)] ![(gy), (gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy), (gx⁻¹ * gy * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_s49 : Reachable ![(gy), (gx⁻¹ * gy)] ![(gy), (gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy), (gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m14_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (standard 2) := by
  have fin : Reachable ![(gy), (gx⁻¹)] (standard 2) := by std_fin
  exact n4m14_s0.trans' (n4m14_s1.trans' (n4m14_s2.trans' (n4m14_s3.trans' (n4m14_s4.trans' (n4m14_s5.trans' (n4m14_s6.trans' (n4m14_s7.trans' (n4m14_s8.trans' (n4m14_s9.trans' (n4m14_s10.trans' (n4m14_s11.trans' (n4m14_s12.trans' (n4m14_s13.trans' (n4m14_s14.trans' (n4m14_s15.trans' (n4m14_s16.trans' (n4m14_s17.trans' (n4m14_s18.trans' (n4m14_s19.trans' (n4m14_s20.trans' (n4m14_s21.trans' (n4m14_s22.trans' (n4m14_s23.trans' (n4m14_s24.trans' (n4m14_s25.trans' (n4m14_s26.trans' (n4m14_s27.trans' (n4m14_s28.trans' (n4m14_s29.trans' (n4m14_s30.trans' (n4m14_s31.trans' (n4m14_s32.trans' (n4m14_s33.trans' (n4m14_s34.trans' (n4m14_s35.trans' (n4m14_s36.trans' (n4m14_s37.trans' (n4m14_s38.trans' (n4m14_s39.trans' (n4m14_s40.trans' (n4m14_s41.trans' (n4m14_s42.trans' (n4m14_s43.trans' (n4m14_s44.trans' (n4m14_s45.trans' (n4m14_s46.trans' (n4m14_s47.trans' (n4m14_s48.trans' (n4m14_s49.trans' (fin))))))))))))))))))))))))))))))))))))))))))))))))))

theorem MS4_wA_m14 : Reachable (MS 4 (wA (-6))) (standard 2) := by
  have h := MS_wA_reduce 4 (-1) (-2)
  rw [show (-1 : ℤ) * ((4 : ℕ) : ℤ) + (-2) = -6 by norm_num] at h
  have e : MS 4 (gy ^ (-(-2 : ℤ)) * gx * gy ^ ((-2 : ℤ) - (-1)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n4m14_path

theorem n4m18_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s1 : Reachable ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s2 : Reachable ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s3 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s4 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s5 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s6 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s7 : Reachable ![(gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s8 : Reachable ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s9 : Reachable ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s10 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s11 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s12 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s13 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s14 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s15 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s16 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s17 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s18 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s19 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s20 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s21 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s22 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s23 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s24 : Reachable ![(gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹), (gy * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_s25 : Reachable ![(gx⁻¹), (gy * gx⁻¹)] ![(gx⁻¹), (gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹), (gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m18_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (standard 2) := by
  have fin : Reachable ![(gx⁻¹), (gy)] (standard 2) := by std_fin
  exact n4m18_s0.trans' (n4m18_s1.trans' (n4m18_s2.trans' (n4m18_s3.trans' (n4m18_s4.trans' (n4m18_s5.trans' (n4m18_s6.trans' (n4m18_s7.trans' (n4m18_s8.trans' (n4m18_s9.trans' (n4m18_s10.trans' (n4m18_s11.trans' (n4m18_s12.trans' (n4m18_s13.trans' (n4m18_s14.trans' (n4m18_s15.trans' (n4m18_s16.trans' (n4m18_s17.trans' (n4m18_s18.trans' (n4m18_s19.trans' (n4m18_s20.trans' (n4m18_s21.trans' (n4m18_s22.trans' (n4m18_s23.trans' (n4m18_s24.trans' (n4m18_s25.trans' (fin))))))))))))))))))))))))))

theorem MS4_wA_m18 : Reachable (MS 4 (wA (-2))) (standard 2) := by
  have h := MS_wA_reduce 4 (0) (-2)
  rw [show (0 : ℤ) * ((4 : ℕ) : ℤ) + (-2) = -2 by norm_num] at h
  have e : MS 4 (gy ^ (-(-2 : ℤ)) * gx * gy ^ ((-2 : ℤ) - (0)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n4m18_path

theorem n4m19_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s1 : Reachable ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s2 : Reachable ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s3 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s4 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s5 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s6 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s7 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s8 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s9 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s10 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s11 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s12 : Reachable ![(gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s13 : Reachable ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gy⁻¹ * gx * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s14 : Reachable ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gy⁻¹ * gx * gx * gy * gx⁻¹)] ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] := reach_of_eq (reach_conj ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gy⁻¹ * gx * gx * gy * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s15 : Reachable ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] := reach_of_eq (reach_mulRight ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s16 : Reachable ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] := reach_of_eq (reach_conj ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s17 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] := reach_of_eq (reach_conj ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s18 : Reachable ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] := reach_of_eq (reach_mulRight ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s19 : Reachable ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s20 : Reachable ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy⁻¹ * gx * gx * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s21 : Reachable ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s22 : Reachable ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s23 : Reachable ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s24 : Reachable ![(gx * gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s25 : Reachable ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s26 : Reachable ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s27 : Reachable ![(gx * gy * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s28 : Reachable ![(gy⁻¹ * gx * gy * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy * gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s29 : Reachable ![(gy⁻¹ * gx * gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s30 : Reachable ![(gx * gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s31 : Reachable ![(gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s32 : Reachable ![(gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s33 : Reachable ![(gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s34 : Reachable ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s35 : Reachable ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s36 : Reachable ![(gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s37 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s38 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s39 : Reachable ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s40 : Reachable ![(gy * gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s41 : Reachable ![(gy * gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s42 : Reachable ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s43 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s44 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s45 : Reachable ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s46 : Reachable ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s47 : Reachable ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s48 : Reachable ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s49 : Reachable ![(gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s50 : Reachable ![(gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s51 : Reachable ![(gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s52 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s53 : Reachable ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s54 : Reachable ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s55 : Reachable ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_inv ![(gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx * gx * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s56 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s57 : Reachable ![(gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s58 : Reachable ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s59 : Reachable ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s60 : Reachable ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s61 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s62 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s63 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s64 : Reachable ![(gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s65 : Reachable ![(gy * gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s66 : Reachable ![(gy * gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s67 : Reachable ![(gx * gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s68 : Reachable ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s69 : Reachable ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s70 : Reachable ![(gx * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s71 : Reachable ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s72 : Reachable ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s73 : Reachable ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s74 : Reachable ![(gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s75 : Reachable ![(gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s76 : Reachable ![(gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s77 : Reachable ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s78 : Reachable ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s79 : Reachable ![(gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s80 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s81 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s82 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s83 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s84 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s85 : Reachable ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s86 : Reachable ![(gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy * gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s87 : Reachable ![(gy * gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy * gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s88 : Reachable ![(gy * gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s89 : Reachable ![(gy * gx * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s90 : Reachable ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s91 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s92 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s93 : Reachable ![(gx * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s94 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s95 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s96 : Reachable ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s97 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s98 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s99 : Reachable ![(gx * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gx * gx * gy⁻¹ * gx * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s100 : Reachable ![(gy⁻¹ * gx * gy * gx * gx * gy⁻¹ * gx * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gx * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gx * gx * gy⁻¹ * gx * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s101 : Reachable ![(gy⁻¹ * gx * gy * gx * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy⁻¹ * gx * gy * gx * gx * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy * gx * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s102 : Reachable ![(gy⁻¹ * gx * gy * gx * gx * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gx * gx * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s103 : Reachable ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s104 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gx * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s105 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s106 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s107 : Reachable ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s108 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s109 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s110 : Reachable ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s111 : Reachable ![(gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s112 : Reachable ![(gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s113 : Reachable ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s114 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s115 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s116 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gy⁻¹ * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s117 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s118 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s119 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s120 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy * gx⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s121 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s122 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s123 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s124 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s125 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s126 : Reachable ![(gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s127 : Reachable ![(gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹), (gy⁻¹ * gx * gx * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s128 : Reachable ![(gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gx)] ![(gx), (gy⁻¹ * gx * gx * gx)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s129 : Reachable ![(gx), (gy⁻¹ * gx * gx * gx)] ![(gx), (gy⁻¹ * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx), (gy⁻¹ * gx * gx * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s130 : Reachable ![(gx), (gy⁻¹ * gx * gx)] ![(gx), (gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gx), (gy⁻¹ * gx * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_s131 : Reachable ![(gx), (gy⁻¹ * gx)] ![(gx), (gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx), (gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n4m19_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] (standard 2) := by
  have fin : Reachable ![(gx), (gy⁻¹)] (standard 2) := by std_fin
  exact n4m19_s0.trans' (n4m19_s1.trans' (n4m19_s2.trans' (n4m19_s3.trans' (n4m19_s4.trans' (n4m19_s5.trans' (n4m19_s6.trans' (n4m19_s7.trans' (n4m19_s8.trans' (n4m19_s9.trans' (n4m19_s10.trans' (n4m19_s11.trans' (n4m19_s12.trans' (n4m19_s13.trans' (n4m19_s14.trans' (n4m19_s15.trans' (n4m19_s16.trans' (n4m19_s17.trans' (n4m19_s18.trans' (n4m19_s19.trans' (n4m19_s20.trans' (n4m19_s21.trans' (n4m19_s22.trans' (n4m19_s23.trans' (n4m19_s24.trans' (n4m19_s25.trans' (n4m19_s26.trans' (n4m19_s27.trans' (n4m19_s28.trans' (n4m19_s29.trans' (n4m19_s30.trans' (n4m19_s31.trans' (n4m19_s32.trans' (n4m19_s33.trans' (n4m19_s34.trans' (n4m19_s35.trans' (n4m19_s36.trans' (n4m19_s37.trans' (n4m19_s38.trans' (n4m19_s39.trans' (n4m19_s40.trans' (n4m19_s41.trans' (n4m19_s42.trans' (n4m19_s43.trans' (n4m19_s44.trans' (n4m19_s45.trans' (n4m19_s46.trans' (n4m19_s47.trans' (n4m19_s48.trans' (n4m19_s49.trans' (n4m19_s50.trans' (n4m19_s51.trans' (n4m19_s52.trans' (n4m19_s53.trans' (n4m19_s54.trans' (n4m19_s55.trans' (n4m19_s56.trans' (n4m19_s57.trans' (n4m19_s58.trans' (n4m19_s59.trans' (n4m19_s60.trans' (n4m19_s61.trans' (n4m19_s62.trans' (n4m19_s63.trans' (n4m19_s64.trans' (n4m19_s65.trans' (n4m19_s66.trans' (n4m19_s67.trans' (n4m19_s68.trans' (n4m19_s69.trans' (n4m19_s70.trans' (n4m19_s71.trans' (n4m19_s72.trans' (n4m19_s73.trans' (n4m19_s74.trans' (n4m19_s75.trans' (n4m19_s76.trans' (n4m19_s77.trans' (n4m19_s78.trans' (n4m19_s79.trans' (n4m19_s80.trans' (n4m19_s81.trans' (n4m19_s82.trans' (n4m19_s83.trans' (n4m19_s84.trans' (n4m19_s85.trans' (n4m19_s86.trans' (n4m19_s87.trans' (n4m19_s88.trans' (n4m19_s89.trans' (n4m19_s90.trans' (n4m19_s91.trans' (n4m19_s92.trans' (n4m19_s93.trans' (n4m19_s94.trans' (n4m19_s95.trans' (n4m19_s96.trans' (n4m19_s97.trans' (n4m19_s98.trans' (n4m19_s99.trans' (n4m19_s100.trans' (n4m19_s101.trans' (n4m19_s102.trans' (n4m19_s103.trans' (n4m19_s104.trans' (n4m19_s105.trans' (n4m19_s106.trans' (n4m19_s107.trans' (n4m19_s108.trans' (n4m19_s109.trans' (n4m19_s110.trans' (n4m19_s111.trans' (n4m19_s112.trans' (n4m19_s113.trans' (n4m19_s114.trans' (n4m19_s115.trans' (n4m19_s116.trans' (n4m19_s117.trans' (n4m19_s118.trans' (n4m19_s119.trans' (n4m19_s120.trans' (n4m19_s121.trans' (n4m19_s122.trans' (n4m19_s123.trans' (n4m19_s124.trans' (n4m19_s125.trans' (n4m19_s126.trans' (n4m19_s127.trans' (n4m19_s128.trans' (n4m19_s129.trans' (n4m19_s130.trans' (n4m19_s131.trans' (fin))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem MS4_wA_m19 : Reachable (MS 4 (wA (-1))) (standard 2) := by
  have h := MS_wA_reduce 4 (0) (-1)
  rw [show (0 : ℤ) * ((4 : ℕ) : ℤ) + (-1) = -1 by norm_num] at h
  have e : MS 4 (gy ^ (-(-1 : ℤ)) * gx * gy ^ ((-1 : ℤ) - (0)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gx⁻¹ * gy⁻¹)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n4m19_path

/-- `MS(4, y^{-m} x y^m x^{-1})` is AC-trivial whenever `m mod 20 ∉ {3,7,9,11,13,17}`. -/
theorem MS4_wA (m : ℤ) (h3 : m % 20 ≠ 3) (h7 : m % 20 ≠ 7) (h9 : m % 20 ≠ 9) (h11 : m % 20 ≠ 11)
    (h13 : m % 20 ≠ 13) (h17 : m % 20 ≠ 17) : Reachable (MS 4 (wA m)) (standard 2) := by
  have hp := MS_wA_period_mul 4 m (-(m / 20))
  have e : m + -(m / 20) * ((((4 : ℕ) : ℤ) + 1) * ((4 : ℕ) : ℤ)) = m % 20 := by
    have := Int.emod_add_mul_ediv m 20; push_cast; linarith
  rw [e] at hp
  refine hp.trans' ?_
  have h0 : 0 ≤ m % 20 := Int.emod_nonneg m (by norm_num)
  have h1 : m % 20 < 20 := Int.emod_lt_of_pos m (by norm_num)
  generalize m % 20 = r at h0 h1 h3 h7 h9 h11 h13 h17 ⊢
  have mult : ∀ q : ℤ, Reachable (MS 4 (wA (q * 4))) (standard 2) := fun q => by
    simpa using MS_wA_mult 4 q
  have msucc : ∀ q : ℤ, Reachable (MS 4 (wA (q * 5))) (standard 2) := fun q => by
    have := MS_wA_mult_succ 4 q; norm_num at this; exact this
  have back : ∀ r : ℤ, Reachable (MS 4 (wA (r - 20))) (standard 2) →
      Reachable (MS 4 (wA r)) (standard 2) := fun r hr => by
    have := MS_wA_period_mul 4 r (-1)
    rw [show r + -1 * ((((4 : ℕ) : ℤ) + 1) * ((4 : ℕ) : ℤ)) = r - 20 by push_cast; ring] at this
    exact this.trans' hr
  interval_cases r
  · simpa using mult 0
  · exact MS_wA_one 4
  · exact MS4_wA_m2
  · exact absurd rfl h3
  · simpa using mult 1
  · simpa using msucc 1
  · exact MS4_wA_m6
  · exact absurd rfl h7
  · simpa using mult 2
  · exact absurd rfl h9
  · simpa using msucc 2
  · exact absurd rfl h11
  · simpa using mult 3
  · exact absurd rfl h13
  · exact back 14 (by simpa using MS4_wA_m14)
  · simpa using msucc 3
  · simpa using mult 4
  · exact absurd rfl h17
  · exact back 18 (by simpa using MS4_wA_m18)
  · exact back 19 (by simpa using MS4_wA_m19)

end AC
