import ACProof.MS2All
import ACProof.Period
import ACProof.N3
import ACProof.N4
import ACProof.Symmetry
open AC
example : Reachable (MS 3 (gy ^ (5:ℤ))) (standard 2) := MS_ypow_reachable 3 5
example : Reachable (MS 7 wstar) (standard 2) := MS_wstar_reachable 7
example : Reachable (MS 2 (wk (-11))) (standard 2) := MS2_wk_reachable (-11)
example : PresentsTrivialGroup (MS 2 (wk 4)) := (MS2_wk_reachable 4).presentsTrivialGroup
#print axioms AC.reach_mul_normalClosure
#print axioms AC.subst_reachable
#print axioms AC.MS_ypow_reachable
#print axioms AC.Reachable.presentsTrivialGroup_iff
#print axioms AC.Reachable.symm
#print axioms AC.reach_mulLeft
#print axioms AC.reach_mulLeft_inv
#print axioms AC.reach_swap
#print axioms AC.reach_perm
#print axioms AC.Reachable.relabel
#print axioms AC.MS1_reachable
#print axioms AC.MS_wstar_reachable
#print axioms AC.MS_wk_equiv
#print axioms AC.MS2_w3_reachable
#print axioms AC.MS2_wk_reachable
#print axioms AC.AK_reach_MS
#print axioms AC.AK2_reachable
#print axioms AC.MS_reach_P
#print axioms AC.MS_wA_neg
#print axioms AC.MS_wA_succ
#print axioms AC.MS_wA_negsucc
#print axioms AC.MS_wA_self
#print axioms AC.MS_wA_diag
#print axioms AC.MS_wA_mult
#print axioms AC.MS_wA_reduce
#print axioms AC.MS2_v_shift
#print axioms AC.MS2_v_reachable
#print axioms AC.MS2_wA_all
example : Reachable (MS 2 (wA 101)) (standard 2) := MS2_wA_all 101

#print axioms AC.MS_wA_period
#print axioms AC.MS_wA_period_mul
#print axioms AC.MS_wA_of_residues
#print axioms AC.MS_wA_mult_succ
#print axioms AC.MS_wA_one
#print axioms AC.MS3_wA_m10
#print axioms AC.MS3_wA_m2
#print axioms AC.MS3_wA_m1
#print axioms AC.MS3_wA
#print axioms AC.MS4_wA_m2
#print axioms AC.MS4_wA_m6
#print axioms AC.MS4_wA_m14
#print axioms AC.MS4_wA_m18
#print axioms AC.MS4_wA_m19
#print axioms AC.MS4_wA
#print axioms AC.MS_wA_negate
#print axioms AC.MS_wA_neg_one
#print axioms AC.MS_wA_pm_one
