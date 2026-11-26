import ACProof.AK1ConjLower

/-! # The four-point image requires at least four relator multiplications -/

namespace AC.AK1Certificate

private def oneSwap (p : P) : Prop := ∃ i j : Fin 4, p = Equiv.swap i j

private def twoSwaps (p : P) : Prop := ∃ a b : P, oneSwap a ∧ oneSwap b ∧ p = a * b

private theorem one_id : oneSwap 1 := ⟨0, 0, by simp; rfl⟩

private theorem one_two {p : P} (h : oneSwap p) : twoSwaps p :=
  ⟨p, 1, h, one_id, by simp⟩

private theorem two_mul {p q : P} (h : oneSwap p) (k : oneSwap q) : twoSwaps (p*q) :=
  ⟨p, q, h, k, rfl⟩

private def respects (f : P → P) : Prop := f 1 = 1 ∧
  (∀ p, oneSwap p → oneSwap (f p)) ∧ (∀ p, twoSwaps p → twoSwaps (f p))

private theorem respects_id : respects id := ⟨rfl, fun _ h => h, fun _ h => h⟩

private theorem respects_inv : respects (fun p : P => p⁻¹) := by
  have hi : ∀ p : P, oneSwap p → oneSwap p⁻¹ := by
    rintro p ⟨i, j, rfl⟩
    exact ⟨i, j, by simp⟩
  refine ⟨inv_one, hi, ?_⟩
  rintro p ⟨a, b, ha, hb, rfl⟩
  exact ⟨b⁻¹, a⁻¹, hi _ hb, hi _ ha, mul_inv_rev _ _⟩

private theorem respects_conj (w : P) : respects (fun p => w*p*w⁻¹) := by
  have hc : ∀ p, oneSwap p → oneSwap (w*p*w⁻¹) := by
    rintro p ⟨i, j, rfl⟩
    exact ⟨w i, w j, (Equiv.swap_apply_apply w i j).symm⟩
  refine ⟨by simp, hc, ?_⟩
  rintro p ⟨a, b, ha, hb, rfl⟩
  exact ⟨_, _, hc a ha, hc b hb, by group⟩

/-- After two multiplications each slot takes at most two swaps. After a third
multiplication the untouched slot still takes at most two swaps. -/
private def profile (k : ℕ) (a b : P) : Prop :=
  (k = 0 → oneSwap a ∧ b = 1) ∧ (k ≤ 1 → oneSwap a ∧ oneSwap b) ∧
  (k ≤ 2 → twoSwaps a ∧ twoSwaps b) ∧ (k ≤ 3 → twoSwaps a ∨ twoSwaps b)

private theorem profile_map {k : ℕ} {a b : P} (h : profile k a b)
    {f g : P → P} (hf : respects f) (hg : respects g) : profile k (f a) (g b) := by
  refine ⟨fun e => ⟨hf.2.1 _ (h.1 e).1, (congrArg g (h.1 e).2).trans hg.1⟩,
    fun e => ⟨hf.2.1 _ (h.2.1 e).1, hg.2.1 _ (h.2.1 e).2⟩,
    fun e => ⟨hf.2.2 _ (h.2.2.1 e).1, hg.2.2 _ (h.2.2.1 e).2⟩, fun e => ?_⟩
  exact (h.2.2.2 e).imp (hf.2.2 _) (hg.2.2 _)

private theorem profile_mul_left {k : ℕ} {a b : P} (h : profile k a b) :
    profile (k+1) (a*b) b := by
  refine ⟨by omega, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨ha, rfl⟩ := h.1 (by omega)
    simpa using And.intro ha one_id
  · obtain ⟨ha, hb⟩ := h.2.1 (by omega)
    exact ⟨two_mul ha hb, one_two hb⟩
  · exact Or.inr (h.2.2.1 (by omega)).2

private theorem profile_mul_right {k : ℕ} {a b : P} (h : profile k a b) :
    profile (k+1) a (b*a) := by
  refine ⟨by omega, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨ha, rfl⟩ := h.1 (by omega)
    simpa using And.intro ha ha
  · obtain ⟨ha, hb⟩ := h.2.1 (by omega)
    exact ⟨one_two ha, two_mul hb ha⟩
  · exact Or.inl (h.2.2.1 (by omega)).1

private theorem initial_profile :
    profile 0 (evalWord (AK 1 0)) (evalWord (AK 1 1)) := by
  have hx : evalWord (AK 1 0) = t := by simp [AK, evalX, evalY]; decide
  have hy : evalWord (AK 1 1) = 1 := by simp [AK, evalX, evalY]; decide
  rw [hx, hy]
  have h : oneSwap t := ⟨2, 3, rfl⟩
  exact ⟨fun _ => ⟨h, rfl⟩, fun _ => ⟨h, one_id⟩,
    fun _ => ⟨one_two h, one_two one_id⟩, fun _ => Or.inl (one_two h)⟩

private theorem trace_profile (ms : List (PrimitiveMove 2)) :
    profile (mulCount ms) (evalWord (runMoves (AK 1) ms 0)) (evalWord (runMoves (AK 1) ms 1)) := by
  induction ms using List.reverseRecOn with
  | nil => exact initial_profile
  | append_singleton ms m ih =>
    rw [runMoves_append, mulCount_append]
    cases m with
    | inv i =>
      fin_cases i
      · simpa [mulCount, PrimitiveMove.mulCost, runMoves, PrimitiveMove.apply] using
          profile_map ih respects_inv respects_id
      · simpa [mulCount, PrimitiveMove.mulCost, runMoves, PrimitiveMove.apply] using
          profile_map ih respects_id respects_inv
    | conj i w =>
      fin_cases i
      · simpa [mulCount, PrimitiveMove.mulCost, runMoves, PrimitiveMove.apply] using
          profile_map ih (respects_conj (evalWord w)) respects_id
      · simpa [mulCount, PrimitiveMove.mulCost, runMoves, PrimitiveMove.apply] using
          profile_map ih respects_id (respects_conj (evalWord w))
    | mulRight i j hij =>
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simpa [mulCount, PrimitiveMove.mulCost, runMoves, PrimitiveMove.apply] using profile_mul_left ih
      · simpa [mulCount, PrimitiveMove.mulCost, runMoves, PrimitiveMove.apply] using profile_mul_right ih
      · exact (hij rfl).elim

set_option maxRecDepth 8000 in
private theorem excludes_standard : ¬twoSwaps X ∧ ¬twoSwaps Y := by
  have test : ∀ i j k l : Fin 4, Equiv.swap i j * Equiv.swap k l ≠ X ∧
      Equiv.swap i j * Equiv.swap k l ≠ Y := by decide
  constructor
  · rintro ⟨a,b,⟨i,j,rfl⟩,⟨k,l,rfl⟩,h⟩
    exact (test i j k l).1 h.symm
  · rintro ⟨a,b,⟨i,j,rfl⟩,⟨k,l,rfl⟩,h⟩
    exact (test i j k l).2 h.symm

theorem _root_.AC.AK1_mulCount_lower (ms : List (PrimitiveMove 2))
    (hend : runMoves (AK 1) ms = standard 2) : 4 ≤ mulCount ms := by
  by_contra! h
  have hp := trace_profile ms
  rw [hend] at hp
  change profile _ (evalWord gx) (evalWord gy) at hp
  rw [evalX, evalY] at hp
  exact (hp.2.2.2 (by omega)).elim excludes_standard.1 excludes_standard.2

end AC.AK1Certificate
