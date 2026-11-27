import ACProof.MS2All
import ACProof.MS2Alt
import ACProof.N3
import ACProof.N4
import ACProof.N5
import ACProof.AK3Link
import ACProof.AK4Link
import ACProof.AKFamily
import ACProof.Comparison
import ACProof.EuclideanWitness
import ACProof.AKProjective
import ACProof.AK1Distance
import ACProof.AK2ConjExact
import ACProof.MSStarThree
import ACProof.MSStarRotation
import ACProof.CyclicRelatorRecovery

/-! Axiom audit for every submission theorem (see README, theorem table). -/
#print axioms AC.msStarOneRotated_witness
#print axioms AC.msStarOneRotated_exact
#print axioms AC.CyclicRelator.undoRotation
#print axioms AC.CyclicRelator.recoverRows
#print axioms AC.MSStarCertificate.odd_lower
#print axioms AC.MSStar_zero_witness
#print axioms AC.MSStar_one_witness
#print axioms AC.MSStarThree.bounds
#print axioms AC.MSStarThree.lower
#print axioms AC.MSStarThree.zero_lower
#print axioms AC.MSStar_zero_conjCount_exact
#print axioms AC.MSStar_one_conjCount_exact
#print axioms AC.ComplementaryInvolutions.lower
#print axioms AC.AK_three_conjugations
#print axioms AC.AK_length_add_seven
#print axioms AC.AK2_threeConjugations_witness
#print axioms AC.AK2_threeConjugations_short_witness
#print axioms AC.AK2_conjCount_exact
#print axioms AC.reach_mul_normalClosure
#print axioms AC.Reachable.presentsTrivialGroup_iff
#print axioms AC.Reachable.symm
#print axioms AC.Reachable.presentsTrivialGroup
#print axioms AC.reach_swap
#print axioms AC.reach_perm
#print axioms AC.reach_mulLeft
#print axioms AC.Reachable.map
#print axioms AC.Reachable.relabel
#print axioms AC.MS1_reachable
#print axioms AC.MS_wstar_reachable
#print axioms AC.MS_wk_succ
#print axioms AC.MS_wk_equiv
#print axioms AC.MS2_wk_reachable
#print axioms AC.AK_reach_MS
#print axioms AC.AK2_reachable
#print axioms AC.MS_reach_P
#print axioms AC.MS_ypow_reachable
#print axioms AC.MS_wA_neg
#print axioms AC.MS_wA_succ
#print axioms AC.MS_wA_negsucc
#print axioms AC.MS_wA_self
#print axioms AC.MS_wA_mult
#print axioms AC.MS_wA_reduce
#print axioms AC.MS_wA_diag
#print axioms AC.MS_wA_period
#print axioms AC.MS_wA_period_mul
#print axioms AC.MS_wA_of_residues
#print axioms AC.MS_wA_mult_succ
#print axioms AC.MS_wA_one
#print axioms AC.MS_wA_negate
#print axioms AC.MS_wA_neg_one
#print axioms AC.MS_wA_pm_one
#print axioms AC.MS_wA_cover
#print axioms AC.MS2_v_shift
#print axioms AC.MS2_v_reachable
#print axioms AC.MS2_wA_all
#print axioms AC.MS2_wA_all'
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
#print axioms AC.link_identity
#print axioms AC.phi_MS3_wA5_reach_wk8
#print axioms AC.MS3_wA5_iff_AK3
#print axioms AC.MS3_wA_of_AK3
#print axioms AC.bs_pow
#print axioms AC.link4_identity
#print axioms AC.phi_MS4_wAm9_reach_wkm9
#print axioms AC.MS4_wAm9_iff_AK4
#print axioms AC.MS4_wA_9_11_of_AK4
#print axioms AC.MS_wA_reach_SnPres
#print axioms AC.SnPres_reach_MS_wA
#print axioms AC.MS5_wA_m2
#print axioms AC.MS5_wA_m3
#print axioms AC.MS5_wA_m27
#print axioms AC.MS5_wA_m28
#print axioms AC.MS5_wA_m9
#print axioms AC.MS5_wA_m21
#print axioms AC.MS5_wA
#print axioms AC.MS_wA_reach_AK
#print axioms AC.MS_wA_period_reach_AK
#print axioms AC.MS_wA_pm_iff_AK
#print axioms AC.MS5_wA_19_reach_AK5
#print axioms AC.MS5_wA_11_19_iff_AK5

#print axioms AC.euclideanCost_comm
#print axioms AC.euclideanCost_zero_left
#print axioms AC.euclideanCost_zero_right
#print axioms AC.euclideanCost_add_left
#print axioms AC.euclideanCost_one_right
#print axioms AC.euclideanCost_mulRight
#print axioms AC.euclideanCost_add_left_le
#print axioms AC.euclideanCost_le_add_left
#print axioms AC.euclideanCost_add_right_le
#print axioms AC.euclideanCost_le_add_right
#print axioms AC.CountedStep.step
#print axioms AC.Step.exists_countedStep
#print axioms AC.reachable_iff_exists_countedPath
#print axioms AC.CountedPath.mulCount_le_length
#print axioms AC.CountedStep.euclideanPotential_bound
#print axioms AC.Step.euclideanPotential_bound
#print axioms AC.CountedPath.euclideanPotential_bound
#print axioms AC.expY_gx
#print axioms AC.expY_gy
#print axioms AC.euclideanPotential_standard
#print axioms AC.euclideanPotential_AK
#print axioms AC.AK_to_standard_mulCount
#print axioms AC.standard_to_AK_mulCount
#print axioms AC.shearTuple_exact
#print axioms AC.expX_gx
#print axioms AC.expX_gy
#print axioms AC.standard_hasIdentityExponents
#print axioms AC.AK_to_identityExponents_nonmul
#print axioms AC.CountedPath.strict_euclideanPotential_bound
#print axioms AC.AK_to_identityExponents_mulCount
#print axioms AC.AK_to_identityFiber_mulCount
#print axioms AC.AK_to_standard_mulCount_sharp
#print axioms AC.AK_identityExponentMatrix_witness
#print axioms AC.AK_identityFiber_exact
#print axioms AC.AK_to_standard_length

#print axioms AC.runMoves_append
#print axioms AC.conjCount_append
#print axioms AC.PrimitiveMove.step
#print axioms AC.Step.exists_primitiveMove
#print axioms AC.runMoves_reachable
#print axioms AC.reachable_iff_exists_runMoves
#print axioms AC.AK1_twoConjugations_witness
#print axioms AC.AK1Certificate.lower
#print axioms AC.AK1_conjCount_lower
#print axioms AC.commute_sq_of_mem_closure_involutions
#print axioms AC.exists_involutions_of_atMostOneConj
#print axioms AC.two_le_conjCount_of_involutionImage
#print axioms AC.AK_length_add_conjCount
#print axioms AC.AK_length_of_two_conjugations
#print axioms AC.AK1_conjCount_exact
#print axioms AC.AK_two_conjugations
#print axioms AC.AK_length_add_six
#print axioms AC.mulCount_append
#print axioms AC.AK1Certificate.evalX
#print axioms AC.AK1Certificate.evalY
#print axioms AC.AK_operation_bounds
#print axioms AC.AK1_mulCount_lower
#print axioms AC.AK1_mulCount_odd
#print axioms AC.AK1_min_operation_counts
#print axioms AC.AK1_distance_exact
