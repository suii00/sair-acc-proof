# Themes
T1 Parametric AC-trivial families via a formal "consequence/substitution calculus" (CHOSEN).
  Value: reusable Lean infrastructure over the official Step; infinite families (MS(n,y^k), substitution thm).
  Provability: high. Novelty: mathematics KNOWN/elementary; Lean formalization against official defs: novelty-unconfirmed
  (no such proofs in official repo). Next targets: Shehper et al. Thm A (MS(1,w) ∀w; MS(n,y^-1xyx^-1) ∀n; MS(2,y^-k x^-1yxy) ∀k) – known results, formalization new-ish.
T2 Stable-AC formal tools: prove StableReachable invariance lemmas (stabilize/destabilize commuting with AC moves,
  "Reachable after stabilization" lemmas), then formalize AK(3) stable trivialization (Shehper v1/Lisitsa 2024 sequence;
  note v2 says MMS misprint undermines the original chain—must check which sequence remains valid).
  Value: medium-high; provability: medium (needs explicit long sequences, verified by kernel/decide). Novelty: result claimed known (status contested); formal proof novelty-unconfirmed.
T3 Invariants / obstructions: formalize that Reachable preserves PresentsTrivialGroup & normal closure (easy), then
  study finer invariants (e.g. Q-/Wall-type, Bridson-style length lower bounds) for restricted move sets.
  Value: high if a genuine new obstruction; provability of anything disproof-relevant: low (no known invariant separates AC classes for trivial group). Novelty: basic invariance known.
