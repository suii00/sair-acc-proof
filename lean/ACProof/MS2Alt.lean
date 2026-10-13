import ACProof.General

/-!
# `MS(2, wA m)` for all `m`, as a corollary of the general families (no search path).

`ℤ = 2ℤ ∪ 3ℤ ∪ (1 + 6ℤ) ∪ (-1 + 6ℤ)`, and each piece is covered by `MS_wA_cover`
(multiples of `n`, multiples of `n+1`, `±1 mod n(n+1)`).
The original proof `MS2_wA_all` (file `MS2All.lean`) uses a 19-move certified search path instead.
-/

namespace AC

theorem MS2_wA_all' (m : ℤ) : Reachable (MS 2 (wA m)) (standard 2) := by
  apply MS_wA_cover 2 m
  push_cast
  have h := Int.emod_add_mul_ediv m 6
  have h0 : 0 ≤ m % 6 := Int.emod_nonneg m (by norm_num)
  have h1 : m % 6 < 6 := Int.emod_lt_of_pos m (by norm_num)
  generalize m % 6 = r at h h0 h1
  generalize m / 6 = k at h
  interval_cases r
  · exact Or.inl ⟨3 * k, by linarith⟩
  · exact Or.inr (Or.inr (Or.inl ⟨k, by linarith⟩))
  · exact Or.inl ⟨3 * k + 1, by linarith⟩
  · exact Or.inr (Or.inl ⟨2 * k + 1, by linarith⟩)
  · exact Or.inl ⟨3 * k + 2, by linarith⟩
  · exact Or.inr (Or.inr (Or.inr ⟨k + 1, by linarith⟩))

end AC
