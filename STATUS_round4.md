# Round 4 status (2026-10-13 JST). Full build OK (warningAsError), no sorry/admit/native_decide; axioms [propext, Classical.choice, Quot.sound]
CORRECTION of round 3: the "m = n+2 solved for all tested n" observation was a MISREADING of the diag table
(columns were m=-6..-1,1..6). Correct easy diagonals: m ∈ {±n, ±(n+1)} and in fact all multiples of n.
New Lean (ACProof/NewFamilies.lean):
- conj_mult: in F/<<r0>>, Y^{-qn} X Y^{qn} = X Y^{-q} for all q ∈ ℤ.
- MS_wA_mult: ∀ n q, MS(n, y^{-qn} x y^{qn} x⁻¹) AC-trivial (covers m=±n; m=0 trivial).
- MS_wA_self (m=n), MS_wA_succ (m=n+1), MS_wA_neg (m=-n), MS_wA_negsucc (m=-(n+1)).
- MS_wA_diag: m ∈ nℤ ∪ {n+1, -(n+1)} ⇒ AC-trivial.
- MS_wA_reduce: ∀ n q j, MS(n, wA(qn+j)) ~ MS(n, y^{-j} x y^{j-q} x⁻¹)   ("reduction mod n").
Search (search/red.out): applying the reduction then greedy (400k nodes): n=2 all |m|<=7 solved;
 unsolved: n=3 m∈{-7,-5,5,7}; n=4 m∈{-7,-3,3,7}; n=5 m∈{-7,-4,-1,1,4,7} (incl. w⋆ case n=5, known trivial by Shehper Thm 3 -> greedy budget limitation).
Open conjecture targets: MS(2, y⁻¹ x y^{1-q} x⁻¹) ∀q (would give MS(2, wA m) ∀m); general j=±1 classes.
Literature/novelty check (round 4):
- Panteleev–Ushakov arXiv:1609.00325 full text (pu.txt): Sec 6.3 treats random MS with n=2 only (tables 2–4 of specific pairs); no parametric families; no wA-type statements.
- Lisitsa 2024 (Ex. Countex. 6, 100168): MS_n(w⋆) trivializations n=3..8 + two conjectures on their structure.
- Lisitsa 2025 (Ex. Countex. 8; SSRN 5100345): 8634-move trivialization of MS_9(w⋆) (Prover9).
- Shehper et al. v2: families MS(1,w), MS(n,w⋆), MS(2,w_k); dataset n<=7, len(w)<=7 (includes wA(m) for |m|<=2 numerically).
- MMS02: AK(n)~MS(n,w1); Prop 1.1 small cases.
- Web search "Miller–Schupp presentations AC trivial infinite family": found nothing beyond above.
Novelty status of MS_wA_mult / succ / negsucc / reduce: NOT FOUND in the checked literature; novelty-plausible but
 mathematically shallow (one substitution modulo r0). Not checked: Google Scholar exhaustive, Myasnikov 1999 tables, Havas–Ramsay data,
 Burns–Macedońska survey full text, the 2025-26 RL/ML follow-ups.
