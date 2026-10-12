# Round 3 status (2026-10-13 JST). Compiled (warningAsError), no sorry/admit/native_decide; axioms [propext, Classical.choice, Quot.sound]
Sources verified: MMS02 = arXiv:math/0302080 (mms.txt): Prop 1.3: <x,y|x^n=y^{n+1}, xyx=yxy> (n>=2) AC-equiv to <x,y|x^-1y^nx=y^{n+1}, x=y^-1x^-1yxy>. Prop 1.1(a): AK(2) AC-trivial ([23] Myasnikov; Gersten stably).
New Lean (ACProof/AK.lean, ACProof/NewFamilies.lean):
- AK n := ![x^n y^{-(n+1)}, xyx(yxy)^-1]; AK_reach_MS: ∀ n, Reachable (AK n) (MS n (wk 1))      [MMS Prop 1.3, all n]
- AK2_reachable: AK(2) AC-trivial (via MS2_wk_reachable 1; independent of MMS Prop 1.1(a))
- P n k def; MS_reach_P: ∀ n k, Reachable (MS n (wk k)) (P n k)                                  [Shehper v2 Thm 7]
- wA m := y^{-m} x y^m x^-1 (m=1 is w⋆). New parametric families, all n:
    MS_wA_neg (m=-n), MS_wA_succ (m=n+1), MS_wA_negsucc (m=-(n+1)).
  Each reduces modulo r0 (Y^n X = X Y^{n+1}) in ONE substitution to MS(n, y^{±1}).
Search data (search/fam.out, diag.py output in report): greedy (≤150k–300k nodes) on MS(n,w) for
  A: w=y^a x y^b x^-1, B: w=x y^a x^-1 y^b, C: y^a x^-1 y^b x y^c, n=2,3, |a|,|b|,|c|<=3; diagonal wA(m), n=2..5, |m|<=6.
  Family B is trivially MS(n, y^{a+b}) after cancellation (not interesting).
  wA(m) solved for m ∈ {-(n+1),-n,n+1,n+2} for all tested n; several other cells unsolved by greedy (NOT evidence of non-triviality).
Novelty: wA families — NOT found in Shehper v2 (only w⋆, w_k, n=1), MMS02, or Lisitsa 2024 (which treats w⋆, n<=8).
  Shehper's dataset (n<=7, len(w)<=7) contains small instances (|m|<=2). Proofs are one-step substitutions -> likely folklore-level;
  status: novelty-unconfirmed, low depth. Not yet checked: Panteleev–Ushakov full text, Lisitsa 2025 (lengthy trivialization) paper.
Conjecture (open here): MS(n, wA(n+2)) AC-trivial ∀n (solved n=2..4 by search; not a single substitution: gives Y^{-2}XY = X^2).
