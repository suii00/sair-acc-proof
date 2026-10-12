# Round 2 status (2026-10-13 JST) — all compiled (warningAsError), no sorry/admit/native_decide, axioms = [propext, Classical.choice, Quot.sound]
Files (live): /workspace/Andrews-Curtis/competition/tools/lean/ACProof/{Consequence,MillerSchupp,Basic,MS1,MSwk,MS2,Check}.lean
Build: lake build AC ACProof
Convention: MS n w = ![x⁻¹ yⁿ x (y^(n+1))⁻¹, x w⁻¹] (x = of 0, y = of 1), matches MS(n,w)=<x,y|x⁻¹yⁿx=y^{n+1}, x=w>.
Proven:
- Reachable.presentsTrivialGroup_iff, Reachable.ncl_eq, Reachable.presentsTrivialGroup, presentsTrivialGroup_standard
- Reachable.symm (Step.reverse), reach_mulLeft, reach_mulLeft_inv, reach_mulRight_inv, reach_swap, reach_perm (any σ, any rank)
- Step.map / Reachable.map (free-group endomorphisms), Reachable.relabel (generator permutations)
- MS1_reachable: ∀ w, expX w = 1 → MS(1,w) AC-trivial          [Shehper v2 Thm 2 / Thm B(i)]
- MS_wstar_reachable: ∀ n, MS(n, y⁻¹xyx⁻¹) AC-trivial            [Thm 3 / Thm B(ii)]
- MS_wk_equiv: ∀ n k k', MS(n,w_k) ~ MS(n,w_k'), w_k=y^{-k}x⁻¹yxy [Thm 6]
- MS2_wk_reachable: ∀ k, MS(2,w_k) AC-trivial                    [Cor 9 / Thm B(iii)]
  (via own explicit 21-move path for MS(2,w_3), search/greedy.py + emit.py, kernel-checked; NOT via AK(2)/MMS)
Note: theorems hold for all n : ℕ incl. n = 0 (paper: n > 0).
Not done: AK(n), P(n,k) (Thm 7), MMS Prop 5, any stable-AC results, full conjectures.
Novelty: all mathematics is KNOWN (Shehper et al. 2024/25); contribution = kernel-checked formalization against official AC.lean (novelty of formalization unconfirmed).
