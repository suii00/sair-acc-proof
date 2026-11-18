import ACProof.General

/-! # `MS(5, wA m)`: certified search paths for residues 2, 3, 27, 28, -21 and -9 (mod 30),
plus the classification theorem `MS5_wA`. Assembled 2026-11-18 from
search/classes.py + emitn2.py output, following the N4.lean pattern. -/

set_option maxHeartbeats 1000000

namespace AC

theorem n5m2_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s1 : Reachable ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s2 : Reachable ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s3 : Reachable ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s4 : Reachable ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s5 : Reachable ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s6 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s7 : Reachable ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s8 : Reachable ![(gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s9 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s10 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s11 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s12 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s13 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s14 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s15 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gx * gy⁻¹ * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s16 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gx * gy⁻¹ * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gx * gy⁻¹ * gx * gx)] 1) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s17 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s18 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s19 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s20 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gy * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s21 : Reachable ![(gx * gy * gy * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gx * gy * gy * gx * gy⁻¹ * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gy * gx * gy⁻¹ * gx * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s22 : Reachable ![(gx * gx * gy * gy * gx * gy⁻¹ * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gx * gx * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gx * gy * gy * gx * gy⁻¹ * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s23 : Reachable ![(gx * gx * gx * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gx * gx * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s24 : Reachable ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s25 : Reachable ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy)] ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s26 : Reachable ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx * gx * gx * gy * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx * gx * gx * gy * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s27 : Reachable ![(gy⁻¹ * gx * gx * gx * gy * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx * gx * gx * gy * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s28 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s29 : Reachable ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s30 : Reachable ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx * gy⁻¹ * gx * gx * gy * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s31 : Reachable ![(gx * gy⁻¹ * gx * gx * gy * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx * gx * gy * gx * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx * gx * gy * gx * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s32 : Reachable ![(gy⁻¹ * gx * gx * gy * gx * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx * gx * gy * gx * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx * gx * gy * gx * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s33 : Reachable ![(gy⁻¹ * gx * gx * gy * gx * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx * gx * gy * gx * gx * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s34 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s35 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s36 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s37 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s38 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s39 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s40 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s41 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s42 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s43 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s44 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s45 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s46 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s47 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gy * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s48 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx)] ![(gx⁻¹), (gx * gy * gx)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx * gy * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s49 : Reachable ![(gx⁻¹), (gx * gy * gx)] ![(gx⁻¹), (gx * gy)] := reach_of_eq (reach_mulRight ![(gx⁻¹), (gx * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s50 : Reachable ![(gx⁻¹), (gx * gy)] ![(gy), (gx * gy)] := reach_of_eq (reach_mulRight ![(gx⁻¹), (gx * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_s51 : Reachable ![(gy), (gx * gy)] ![(gy), (gx)] := reach_of_eq (reach_mulRight_inv ![(gy), (gx * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m2_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (standard 2) := by
  have fin : Reachable ![(gy), (gx)] (standard 2) := by std_fin
  exact n5m2_s0.trans' (n5m2_s1.trans' (n5m2_s2.trans' (n5m2_s3.trans' (n5m2_s4.trans' (n5m2_s5.trans' (n5m2_s6.trans' (n5m2_s7.trans' (n5m2_s8.trans' (n5m2_s9.trans' (n5m2_s10.trans' (n5m2_s11.trans' (n5m2_s12.trans' (n5m2_s13.trans' (n5m2_s14.trans' (n5m2_s15.trans' (n5m2_s16.trans' (n5m2_s17.trans' (n5m2_s18.trans' (n5m2_s19.trans' (n5m2_s20.trans' (n5m2_s21.trans' (n5m2_s22.trans' (n5m2_s23.trans' (n5m2_s24.trans' (n5m2_s25.trans' (n5m2_s26.trans' (n5m2_s27.trans' (n5m2_s28.trans' (n5m2_s29.trans' (n5m2_s30.trans' (n5m2_s31.trans' (n5m2_s32.trans' (n5m2_s33.trans' (n5m2_s34.trans' (n5m2_s35.trans' (n5m2_s36.trans' (n5m2_s37.trans' (n5m2_s38.trans' (n5m2_s39.trans' (n5m2_s40.trans' (n5m2_s41.trans' (n5m2_s42.trans' (n5m2_s43.trans' (n5m2_s44.trans' (n5m2_s45.trans' (n5m2_s46.trans' (n5m2_s47.trans' (n5m2_s48.trans' (n5m2_s49.trans' (n5m2_s50.trans' (n5m2_s51.trans' (fin))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem MS5_wA_m2 : Reachable (MS 5 (wA (2))) (standard 2) := by
  have h := MS_wA_reduce 5 (0) (2)
  rw [show (0 : ℤ) * ((5 : ℕ) : ℤ) + (2) = 2 by norm_num] at h
  have e : MS 5 (gy ^ (-(2 : ℤ)) * gx * gy ^ ((2 : ℤ) - (0)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n5m2_path

theorem n5m3_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s1 : Reachable ![(gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s2 : Reachable ![(gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s3 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s4 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s5 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s6 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s7 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s8 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s9 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s10 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s11 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s12 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s13 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s14 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s15 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s16 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s17 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s18 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx * gy)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gy * gy * gx * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s19 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gy * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s20 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s21 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s22 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s23 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx * gy)] ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gy * gx * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s24 : Reachable ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s25 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy * gx)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s26 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s27 : Reachable ![(gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹)] ![(gx⁻¹ * gy⁻¹), (gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s28 : Reachable ![(gx⁻¹ * gy⁻¹), (gx⁻¹)] ![(gy * gx), (gx⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy⁻¹), (gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m3_s29 : Reachable ![(gy * gx), (gx⁻¹)] ![(gy), (gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gx), (gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m3_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (standard 2) := by
  have fin : Reachable ![(gy), (gx⁻¹)] (standard 2) := by std_fin
  exact n5m3_s0.trans' (n5m3_s1.trans' (n5m3_s2.trans' (n5m3_s3.trans' (n5m3_s4.trans' (n5m3_s5.trans' (n5m3_s6.trans' (n5m3_s7.trans' (n5m3_s8.trans' (n5m3_s9.trans' (n5m3_s10.trans' (n5m3_s11.trans' (n5m3_s12.trans' (n5m3_s13.trans' (n5m3_s14.trans' (n5m3_s15.trans' (n5m3_s16.trans' (n5m3_s17.trans' (n5m3_s18.trans' (n5m3_s19.trans' (n5m3_s20.trans' (n5m3_s21.trans' (n5m3_s22.trans' (n5m3_s23.trans' (n5m3_s24.trans' (n5m3_s25.trans' (n5m3_s26.trans' (n5m3_s27.trans' (n5m3_s28.trans' (n5m3_s29.trans' (fin))))))))))))))))))))))))))))))


theorem MS5_wA_m3 : Reachable (MS 5 (wA (3))) (standard 2) := by
  have h := MS_wA_reduce 5 (1) (-2)
  rw [show (1 : ℤ) * ((5 : ℕ) : ℤ) + (-2) = 3 by norm_num] at h
  have e : MS 5 (gy ^ (-((-2) : ℤ)) * gx * gy ^ (((-2) : ℤ) - (1)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n5m3_path

theorem n5m27_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s1 : Reachable ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s2 : Reachable ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s3 : Reachable ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s4 : Reachable ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s5 : Reachable ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s6 : Reachable ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s7 : Reachable ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s8 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s9 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s10 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s11 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s12 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s13 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s14 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s15 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s16 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gy * gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s17 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s18 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s19 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s20 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s21 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s22 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s23 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx * gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s24 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹), (gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹), (gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s25 : Reachable ![(gx⁻¹ * gy * gx⁻¹), (gx⁻¹)] ![(gx⁻¹ * gy), (gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gx⁻¹), (gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s26 : Reachable ![(gx⁻¹ * gy), (gx⁻¹)] ![(gy⁻¹ * gx), (gx⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy), (gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m27_s27 : Reachable ![(gy⁻¹ * gx), (gx⁻¹)] ![(gy⁻¹), (gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx), (gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m27_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] (standard 2) := by
  have fin : Reachable ![(gy⁻¹), (gx⁻¹)] (standard 2) := by std_fin
  exact n5m27_s0.trans' (n5m27_s1.trans' (n5m27_s2.trans' (n5m27_s3.trans' (n5m27_s4.trans' (n5m27_s5.trans' (n5m27_s6.trans' (n5m27_s7.trans' (n5m27_s8.trans' (n5m27_s9.trans' (n5m27_s10.trans' (n5m27_s11.trans' (n5m27_s12.trans' (n5m27_s13.trans' (n5m27_s14.trans' (n5m27_s15.trans' (n5m27_s16.trans' (n5m27_s17.trans' (n5m27_s18.trans' (n5m27_s19.trans' (n5m27_s20.trans' (n5m27_s21.trans' (n5m27_s22.trans' (n5m27_s23.trans' (n5m27_s24.trans' (n5m27_s25.trans' (n5m27_s26.trans' (n5m27_s27.trans' (fin))))))))))))))))))))))))))))


theorem MS5_wA_m27 : Reachable (MS 5 (wA (-3))) (standard 2) := by
  have h := MS_wA_reduce 5 (-1) (2)
  rw [show (-1 : ℤ) * ((5 : ℕ) : ℤ) + (2) = -3 by norm_num] at h
  have e : MS 5 (gy ^ (-(2 : ℤ)) * gx * gy ^ ((2 : ℤ) - (-1)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n5m27_path

theorem n5m28_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_inv ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s1 : Reachable ![(gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s2 : Reachable ![(gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s3 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s4 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s5 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s6 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s7 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s8 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s9 : Reachable ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s10 : Reachable ![(gx⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s11 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s12 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹ * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s13 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gy * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s14 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gy * gx⁻¹ * gy⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy * gy * gx⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s15 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s16 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s17 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gx * gy * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gy * gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s18 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gx * gy * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy)] := reach_of_eq (reach_inv ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gy⁻¹ * gx * gx * gx * gy * gx * gx)] 1) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s19 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s20 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s21 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gx)] ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s22 : Reachable ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gx * gy⁻¹ * gy⁻¹ * gx * gy * gx * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_inv ![(gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s23 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gx * gy * gx * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gx * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gy⁻¹ * gx * gy * gx * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s24 : Reachable ![(gx * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s25 : Reachable ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx * gx * gx * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s26 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s27 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s28 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gx * gx * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s29 : Reachable ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_inv ![(gy * gx * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s30 : Reachable ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s31 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s32 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s33 : Reachable ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gx * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s34 : Reachable ![(gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gx * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s35 : Reachable ![(gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_inv ![(gy * gx * gx * gy⁻¹ * gx * gx * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s36 : Reachable ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s37 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s38 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s39 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s40 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s41 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s42 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s43 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy * gx * gy⁻¹ * gx⁻¹ * gx⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s44 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s45 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s46 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s47 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s48 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s49 : Reachable ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx)] ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s50 : Reachable ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx)] ![(gx⁻¹), (gx * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s51 : Reachable ![(gx⁻¹), (gx * gy⁻¹ * gx)] ![(gx⁻¹), (gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹), (gx * gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s52 : Reachable ![(gx⁻¹), (gx * gy⁻¹)] ![(gy⁻¹), (gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹), (gx * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_s53 : Reachable ![(gy⁻¹), (gx * gy⁻¹)] ![(gy⁻¹), (gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹), (gx * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m28_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] (standard 2) := by
  have fin : Reachable ![(gy⁻¹), (gx)] (standard 2) := by std_fin
  exact n5m28_s0.trans' (n5m28_s1.trans' (n5m28_s2.trans' (n5m28_s3.trans' (n5m28_s4.trans' (n5m28_s5.trans' (n5m28_s6.trans' (n5m28_s7.trans' (n5m28_s8.trans' (n5m28_s9.trans' (n5m28_s10.trans' (n5m28_s11.trans' (n5m28_s12.trans' (n5m28_s13.trans' (n5m28_s14.trans' (n5m28_s15.trans' (n5m28_s16.trans' (n5m28_s17.trans' (n5m28_s18.trans' (n5m28_s19.trans' (n5m28_s20.trans' (n5m28_s21.trans' (n5m28_s22.trans' (n5m28_s23.trans' (n5m28_s24.trans' (n5m28_s25.trans' (n5m28_s26.trans' (n5m28_s27.trans' (n5m28_s28.trans' (n5m28_s29.trans' (n5m28_s30.trans' (n5m28_s31.trans' (n5m28_s32.trans' (n5m28_s33.trans' (n5m28_s34.trans' (n5m28_s35.trans' (n5m28_s36.trans' (n5m28_s37.trans' (n5m28_s38.trans' (n5m28_s39.trans' (n5m28_s40.trans' (n5m28_s41.trans' (n5m28_s42.trans' (n5m28_s43.trans' (n5m28_s44.trans' (n5m28_s45.trans' (n5m28_s46.trans' (n5m28_s47.trans' (n5m28_s48.trans' (n5m28_s49.trans' (n5m28_s50.trans' (n5m28_s51.trans' (n5m28_s52.trans' (n5m28_s53.trans' (fin))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem MS5_wA_m28 : Reachable (MS 5 (wA (-2))) (standard 2) := by
  have h := MS_wA_reduce 5 (0) (-2)
  rw [show (0 : ℤ) * ((5 : ℕ) : ℤ) + (-2) = -2 by norm_num] at h
  have e : MS 5 (gy ^ (-((-2) : ℤ)) * gx * gy ^ (((-2) : ℤ) - (0)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n5m28_path

theorem n5m9_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s1 : Reachable ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s2 : Reachable ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s3 : Reachable ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s4 : Reachable ![(gy * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s5 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s6 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s7 : Reachable ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gy⁻¹ * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s8 : Reachable ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s9 : Reachable ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight ![(gy * gx⁻¹ * gy * gy * gy * gy * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s10 : Reachable ![(gy * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s11 : Reachable ![(gx * gy * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gx⁻¹ * gy * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy * gx⁻¹ * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s12 : Reachable ![(gy⁻¹ * gx * gy * gx⁻¹ * gy * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx * gy * gx⁻¹ * gy * gy * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s13 : Reachable ![(gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx⁻¹ * gy * gx * gx * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s14 : Reachable ![(gx⁻¹ * gy * gx * gx * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gy * gx * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx * gx * gy⁻¹ * gx⁻¹ * gy), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s15 : Reachable ![(gy * gx * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s16 : Reachable ![(gx * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s17 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx⁻¹ * gy * gx * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_inv ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)] 1) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s18 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx⁻¹ * gy * gx * gy * gy * gy * gx⁻¹)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gy * gx * gy * gy * gy * gx⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx⁻¹ * gy * gx * gy * gy * gy * gx⁻¹)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s19 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gy * gx * gy * gy * gy * gx⁻¹ * gx⁻¹)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gy * gx * gy * gy * gy * gx⁻¹ * gx⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s20 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gx * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s21 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_mulRight_inv ![(gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s22 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s23 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s24 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s25 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s26 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gy * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gy * gy)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s27 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gy * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gy * gy * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s28 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy * gx)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s29 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s30 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s31 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s32 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s33 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹ * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹ * gy * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s34 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹ * gy)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹ * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s35 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gy * gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s36 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gy * gx⁻¹ * gy * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s37 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s38 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s39 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s40 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gx * gy * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s41 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy * gy * gx * gy⁻¹ * gy⁻¹)] 1) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s42 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s43 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s44 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s45 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s46 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s47 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s48 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s49 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight ![(gy * gy * gx⁻¹ * gy⁻¹ * gx * gy * gx⁻¹ * gy), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s50 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s51 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s52 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s53 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s54 : Reachable ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s55 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s56 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s57 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s58 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx * gx * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s59 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s60 : Reachable ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s61 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy)] := reach_of_eq (reach_inv ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gy * gx)] 1) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s62 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy)] ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s63 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s64 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s65 : Reachable ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s66 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s67 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s68 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gy⁻¹ * gx), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s69 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s70 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s71 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gx * gy⁻¹)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gx * gy⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s72 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gx)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy * gx)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s73 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s74 : Reachable ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_inv ![(gy⁻¹ * gx⁻¹ * gy * gy * gy * gx * gy⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] 0) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s75 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s76 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s77 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s78 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s79 : Reachable ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s80 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gx * gy⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s81 : Reachable ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gy⁻¹ * gx * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s82 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gy⁻¹ * gx⁻¹ * gy * gx * gy⁻¹ * gx)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s83 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_mulRight ![(gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s84 : Reachable ![(gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s85 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s86 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s87 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gy⁻¹ * gx), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s88 : Reachable ![(gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s89 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s90 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gx⁻¹ * gy * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s91 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gy)] ![(gy⁻¹ * gy⁻¹ * gx * gy), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s92 : Reachable ![(gy⁻¹ * gy⁻¹ * gx * gy), (gx⁻¹ * gy * gy)] ![(gy⁻¹ * gx), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gy⁻¹ * gx * gy), (gx⁻¹ * gy * gy)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s93 : Reachable ![(gy⁻¹ * gx), (gx⁻¹ * gy * gy)] ![(gy), (gx⁻¹ * gy * gy)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx), (gx⁻¹ * gy * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s94 : Reachable ![(gy), (gx⁻¹ * gy * gy)] ![(gy), (gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy), (gx⁻¹ * gy * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_s95 : Reachable ![(gy), (gx⁻¹ * gy)] ![(gy), (gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy), (gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m9_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] (standard 2) := by
  have fin : Reachable ![(gy), (gx⁻¹)] (standard 2) := by std_fin
  exact n5m9_s0.trans' (n5m9_s1.trans' (n5m9_s2.trans' (n5m9_s3.trans' (n5m9_s4.trans' (n5m9_s5.trans' (n5m9_s6.trans' (n5m9_s7.trans' (n5m9_s8.trans' (n5m9_s9.trans' (n5m9_s10.trans' (n5m9_s11.trans' (n5m9_s12.trans' (n5m9_s13.trans' (n5m9_s14.trans' (n5m9_s15.trans' (n5m9_s16.trans' (n5m9_s17.trans' (n5m9_s18.trans' (n5m9_s19.trans' (n5m9_s20.trans' (n5m9_s21.trans' (n5m9_s22.trans' (n5m9_s23.trans' (n5m9_s24.trans' (n5m9_s25.trans' (n5m9_s26.trans' (n5m9_s27.trans' (n5m9_s28.trans' (n5m9_s29.trans' (n5m9_s30.trans' (n5m9_s31.trans' (n5m9_s32.trans' (n5m9_s33.trans' (n5m9_s34.trans' (n5m9_s35.trans' (n5m9_s36.trans' (n5m9_s37.trans' (n5m9_s38.trans' (n5m9_s39.trans' (n5m9_s40.trans' (n5m9_s41.trans' (n5m9_s42.trans' (n5m9_s43.trans' (n5m9_s44.trans' (n5m9_s45.trans' (n5m9_s46.trans' (n5m9_s47.trans' (n5m9_s48.trans' (n5m9_s49.trans' (n5m9_s50.trans' (n5m9_s51.trans' (n5m9_s52.trans' (n5m9_s53.trans' (n5m9_s54.trans' (n5m9_s55.trans' (n5m9_s56.trans' (n5m9_s57.trans' (n5m9_s58.trans' (n5m9_s59.trans' (n5m9_s60.trans' (n5m9_s61.trans' (n5m9_s62.trans' (n5m9_s63.trans' (n5m9_s64.trans' (n5m9_s65.trans' (n5m9_s66.trans' (n5m9_s67.trans' (n5m9_s68.trans' (n5m9_s69.trans' (n5m9_s70.trans' (n5m9_s71.trans' (n5m9_s72.trans' (n5m9_s73.trans' (n5m9_s74.trans' (n5m9_s75.trans' (n5m9_s76.trans' (n5m9_s77.trans' (n5m9_s78.trans' (n5m9_s79.trans' (n5m9_s80.trans' (n5m9_s81.trans' (n5m9_s82.trans' (n5m9_s83.trans' (n5m9_s84.trans' (n5m9_s85.trans' (n5m9_s86.trans' (n5m9_s87.trans' (n5m9_s88.trans' (n5m9_s89.trans' (n5m9_s90.trans' (n5m9_s91.trans' (n5m9_s92.trans' (n5m9_s93.trans' (n5m9_s94.trans' (n5m9_s95.trans' (fin))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem MS5_wA_m9 : Reachable (MS 5 (wA (-21))) (standard 2) := by
  have h := MS_wA_reduce 5 (-4) (-1)
  rw [show (-4 : ℤ) * ((5 : ℕ) : ℤ) + (-1) = -21 by norm_num] at h
  have e : MS 5 (gy ^ (-((-1) : ℤ)) * gx * gy ^ (((-1) : ℤ) - (-4)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy⁻¹)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n5m9_path

theorem n5m21_s0 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s1 : Reachable ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s2 : Reachable ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s3 : Reachable ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s4 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s5 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gx⁻¹ * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s6 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s7 : Reachable ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s8 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s9 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy * gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s10 : Reachable ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹ * gy), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s11 : Reachable ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gy * gx⁻¹ * gy⁻¹ * gx⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s12 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gx⁻¹ * gy * gx * gy⁻¹ * gx⁻¹ * gy)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s13 : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gy * gy * gy * gx⁻¹ * gy⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s14 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gy * gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s15 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s16 : Reachable ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s17 : Reachable ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s18 : Reachable ![(gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy * gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gy * gx⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s19 : Reachable ![(gy * gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s20 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gx⁻¹ * gy * gx * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gx⁻¹ * gy * gy * gx⁻¹ * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s21 : Reachable ![(gy * gx⁻¹ * gx⁻¹ * gy * gx * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gx⁻¹ * gy * gx * gy * gx⁻¹), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] 0 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s22 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx * gy), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s23 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx), (gx * gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s24 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] ![(gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy * gx⁻¹ * gx⁻¹ * gy * gx), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s25 : Reachable ![(gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] ![(gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx * gy), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s26 : Reachable ![(gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx * gy * gy), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s27 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy * gx)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s28 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gy * gx * gy⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s29 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] ![(gy * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy * gx⁻¹ * gy⁻¹ * gx * gy * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s30 : Reachable ![(gy * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gy * gy * gx⁻¹)] ![(gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy), (gx⁻¹ * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy * gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx), (gx⁻¹ * gy * gy * gy * gx⁻¹)] 0 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s31 : Reachable ![(gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy), (gx⁻¹ * gy * gy * gy * gx⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx * gy), (gx⁻¹ * gy * gy * gy * gx⁻¹)] 0 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s32 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s33 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gy * gx⁻¹ * gy * gx⁻¹ * gy)] 1 gx) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s34 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹)] 1 gy⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s35 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gx⁻¹ * gy * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s36 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gy * gx⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gy * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gy * gx⁻¹)] 1 gx⁻¹) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s37 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gy * gy)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gx⁻¹ * gy)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gx⁻¹ * gy * gx⁻¹ * gy * gy)] 1 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s38 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gx⁻¹ * gy)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gx⁻¹ * gy * gx⁻¹ * gy)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s39 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gy * gx⁻¹)] ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight_inv ![(gy⁻¹ * gx * gy⁻¹ * gx * gy * gx⁻¹), (gy * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s40 : Reachable ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gy * gy * gx⁻¹)] ![(gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹)] := reach_of_eq (reach_conj ![(gy⁻¹ * gx * gy⁻¹ * gx * gy⁻¹), (gy * gy * gx⁻¹)] 0 gy) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s41 : Reachable ![(gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹)] ![(gx * gy⁻¹), (gy * gy * gx⁻¹)] := reach_of_eq (reach_mulRight ![(gx * gy⁻¹ * gx * gy⁻¹ * gy⁻¹), (gy * gy * gx⁻¹)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s42 : Reachable ![(gx * gy⁻¹), (gy * gy * gx⁻¹)] ![(gx * gy⁻¹), (gy)] := reach_of_eq (reach_mulRight ![(gx * gy⁻¹), (gy * gy * gx⁻¹)] (i := 1) (j := 0) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_s43 : Reachable ![(gx * gy⁻¹), (gy)] ![(gx), (gy)] := reach_of_eq (reach_mulRight ![(gx * gy⁻¹), (gy)] (i := 0) (j := 1) (by decide)) (by apply fin2_ext <;> step_tac3)

theorem n5m21_path : Reachable ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] (standard 2) := by
  have fin : Reachable ![(gx), (gy)] (standard 2) := by std_fin
  exact n5m21_s0.trans' (n5m21_s1.trans' (n5m21_s2.trans' (n5m21_s3.trans' (n5m21_s4.trans' (n5m21_s5.trans' (n5m21_s6.trans' (n5m21_s7.trans' (n5m21_s8.trans' (n5m21_s9.trans' (n5m21_s10.trans' (n5m21_s11.trans' (n5m21_s12.trans' (n5m21_s13.trans' (n5m21_s14.trans' (n5m21_s15.trans' (n5m21_s16.trans' (n5m21_s17.trans' (n5m21_s18.trans' (n5m21_s19.trans' (n5m21_s20.trans' (n5m21_s21.trans' (n5m21_s22.trans' (n5m21_s23.trans' (n5m21_s24.trans' (n5m21_s25.trans' (n5m21_s26.trans' (n5m21_s27.trans' (n5m21_s28.trans' (n5m21_s29.trans' (n5m21_s30.trans' (n5m21_s31.trans' (n5m21_s32.trans' (n5m21_s33.trans' (n5m21_s34.trans' (n5m21_s35.trans' (n5m21_s36.trans' (n5m21_s37.trans' (n5m21_s38.trans' (n5m21_s39.trans' (n5m21_s40.trans' (n5m21_s41.trans' (n5m21_s42.trans' (n5m21_s43.trans' (fin))))))))))))))))))))))))))))))))))))))))))))


theorem MS5_wA_m21 : Reachable (MS 5 (wA (-9))) (standard 2) := by
  have h := MS_wA_reduce 5 (-2) (1)
  rw [show (-2 : ℤ) * ((5 : ℕ) : ℤ) + (1) = -9 by norm_num] at h
  have e : MS 5 (gy ^ (-(1 : ℤ)) * gx * gy ^ ((1 : ℤ) - (-2)) * gx⁻¹) = ![(gx⁻¹ * gy * gy * gy * gy * gy * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹ * gy⁻¹), (gx * gx * gy⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy)] := by
    ms_eq_tac
  rw [e] at h; exact h.trans' n5m21_path

theorem MS5_wA (m : ℤ) (h4 : m % 30 ≠ 4) (h7 : m % 30 ≠ 7) (h8 : m % 30 ≠ 8)
    (h11 : m % 30 ≠ 11) (h13 : m % 30 ≠ 13) (h14 : m % 30 ≠ 14)
    (h16 : m % 30 ≠ 16) (h17 : m % 30 ≠ 17) (h19 : m % 30 ≠ 19)     (h22 : m % 30 ≠ 22) (h23 : m % 30 ≠ 23) (h26 : m % 30 ≠ 26) :
    Reachable (MS 5 (wA m)) (standard 2) := by
  have hp := MS_wA_period_mul 5 m (-(m / 30))
  have e : m + -(m / 30) * ((((5 : ℕ) : ℤ) + 1) * ((5 : ℕ) : ℤ)) = m % 30 := by
    have := Int.emod_add_mul_ediv m 30; push_cast; linarith
  rw [e] at hp
  refine hp.trans' ?_
  have h0 : 0 ≤ m % 30 := Int.emod_nonneg m (by norm_num)
  have h1 : m % 30 < 30 := Int.emod_lt_of_pos m (by norm_num)
  generalize m % 30 = r at h0 h1 h4 h7 h8 h11 h13 h14 h16 h17 h19 h22 h23 h26 ⊢
  have mult : ∀ q : ℤ, Reachable (MS 5 (wA (q * 5))) (standard 2) := fun q => by
    simpa using MS_wA_mult 5 q
  have msucc : ∀ q : ℤ, Reachable (MS 5 (wA (q * 6))) (standard 2) := fun q => by
    have := MS_wA_mult_succ 5 q; norm_num at this; exact this
  have back : ∀ r : ℤ, Reachable (MS 5 (wA (r - 30))) (standard 2) →
      Reachable (MS 5 (wA r)) (standard 2) := fun r hr => by
    have := MS_wA_period_mul 5 r (-1)
    rw [show r + -1 * ((((5 : ℕ) : ℤ) + 1) * ((5 : ℕ) : ℤ)) = r - 30 by push_cast; ring] at this
    exact this.trans' hr
  interval_cases r
  · simpa using mult 0
  · exact MS_wA_one 5
  · exact MS5_wA_m2
  · exact MS5_wA_m3
  · exact absurd rfl h4
  · simpa using mult 1
  · simpa using msucc 1
  · exact absurd rfl h7
  · exact absurd rfl h8
  · exact back 9 (by simpa using MS5_wA_m9)
  · simpa using mult 2
  · exact absurd rfl h11
  · simpa using msucc 2
  · exact absurd rfl h13
  · exact absurd rfl h14
  · simpa using mult 3
  · exact absurd rfl h16
  · exact absurd rfl h17
  · simpa using msucc 3
  · exact absurd rfl h19
  · simpa using mult 4
  · exact back 21 (by simpa using MS5_wA_m21)
  · exact absurd rfl h22
  · exact absurd rfl h23
  · simpa using msucc 4
  · simpa using mult 5
  · exact absurd rfl h26
  · exact back 27 (by simpa using MS5_wA_m27)
  · exact back 28 (by simpa using MS5_wA_m28)
  · exact back 29 (by simpa using MS_wA_neg_one 5)

end AC
