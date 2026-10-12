import ACProof.MS2All

/-!
# Periodicity: `MS(n, wA m) ~ MS(n, wA (m + n(n+1)))` for all `n : ℕ`, `m : ℤ`.

In `BS(n,n+1) = F/⟨⟨x⁻¹yⁿxy^{-(n+1)}⟩⟩` the relator `x·wA(m+n(n+1))⁻¹` is the conjugate by
`y^{n²}` of `x·wA(m)⁻¹`. Hence for each `n` the family `MS(n, wA m)` has at most `n(n+1)`
AC-classes, indexed by `m mod n(n+1)`.
-/

namespace AC

section Per
variable {Q : Type*} [Group Q] {X Y : Q}

theorem P1 (n : ℕ) (hK : Y ^ (n : ℤ) * X = X * Y ^ ((n : ℤ) + 1)) (k : ℤ) :
    X * Y ^ (((n : ℤ) + 1) * k) * X⁻¹ = Y ^ ((n : ℤ) * k) := by
  have h0 : X * Y ^ ((n : ℤ) + 1) * X⁻¹ = Y ^ (n : ℤ) := by
    rw [← hK]; group
  rw [zpow_mul, ← conj_zpow, h0, ← zpow_mul]

theorem period_identity (n : ℕ) (hK : Y ^ (n : ℤ) * X = X * Y ^ ((n : ℤ) + 1)) (m : ℤ) :
    X * (Y ^ (-(m + ((n : ℤ) + 1) * n)) * X * Y ^ (m + ((n : ℤ) + 1) * n) * X⁻¹)⁻¹ =
      Y ^ ((n : ℤ) * n) * (X * (Y ^ (-m) * X * Y ^ m * X⁻¹)⁻¹) * (Y ^ ((n : ℤ) * n))⁻¹ := by
  have Pa := P1 n hK (-(n : ℤ))
  have Pb := P1 n hK ((n : ℤ) + 1)
  have Pc := P1 n hK (n : ℤ)
  have comm : Y ^ ((n : ℤ) * ((n : ℤ) + 1)) * (X * Y ^ (-m) * X⁻¹) =
      (X * Y ^ (-m) * X⁻¹) * Y ^ ((n : ℤ) * ((n : ℤ) + 1)) := by
    rw [← Pb]; group
  have hX : Y ^ ((n : ℤ) * n) * X = X * Y ^ (((n : ℤ) + 1) * n) := by
    rw [← Pc]; group
  calc X * (Y ^ (-(m + ((n : ℤ) + 1) * n)) * X * Y ^ (m + ((n : ℤ) + 1) * n) * X⁻¹)⁻¹
      = X * (X * Y ^ (-m) * X⁻¹) * (X * Y ^ (((n : ℤ) + 1) * -(n : ℤ)) * X⁻¹)
          * Y ^ (m + ((n : ℤ) + 1) * n) := by group
    _ = X * (X * Y ^ (-m) * X⁻¹) * Y ^ ((n : ℤ) * -(n : ℤ)) * Y ^ (m + ((n : ℤ) + 1) * n) := by
        rw [Pa]
    _ = X * ((X * Y ^ (-m) * X⁻¹) * Y ^ ((n : ℤ) * ((n : ℤ) + 1))) * Y ^ (m - (n : ℤ) * n) := by
        group
    _ = X * (Y ^ ((n : ℤ) * ((n : ℤ) + 1)) * (X * Y ^ (-m) * X⁻¹)) * Y ^ (m - (n : ℤ) * n) := by
        rw [comm]
    _ = (X * Y ^ (((n : ℤ) + 1) * n)) * (X * Y ^ (-m) * X⁻¹) * Y ^ (m - (n : ℤ) * n) := by
        group
    _ = (Y ^ ((n : ℤ) * n) * X) * (X * Y ^ (-m) * X⁻¹) * Y ^ (m - (n : ℤ) * n) := by rw [hX]
    _ = _ := by group
end Per

/-- **Period.** `MS(n, wA m)` reaches `MS(n, wA (m + n(n+1)))`. -/
theorem MS_wA_period (n : ℕ) (m : ℤ) :
    Reachable (MS n (wA m)) (MS n (wA (m + ((n : ℤ) + 1) * n))) := by
  have s1 := reach_slot1_conj (MS n (wA m) 0) (gx * (wA m)⁻¹) (gy ^ ((n : ℤ) * n))
  refine s1.trans' (reach_slot1_mod _ _ _ ?_)
  simp only [wA, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  exact (period_identity n (K_rel n) m).symm

theorem MS_wA_period_mul (n : ℕ) (m t : ℤ) :
    Reachable (MS n (wA m)) (MS n (wA (m + t * (((n : ℤ) + 1) * n)))) := by
  have up : ∀ (m : ℤ) (k : ℕ),
      Reachable (MS n (wA m)) (MS n (wA (m + (k : ℤ) * (((n : ℤ) + 1) * n)))) := by
    intro m k
    induction k with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ k ih =>
      have := MS_wA_period n (m + (k : ℤ) * (((n : ℤ) + 1) * n))
      have e : m + ((k + 1 : ℕ) : ℤ) * (((n : ℤ) + 1) * n)
          = m + (k : ℤ) * (((n : ℤ) + 1) * n) + ((n : ℤ) + 1) * n := by push_cast; ring
      rw [e]; exact ih.trans' this
  rcases Int.eq_nat_or_neg t with ⟨k, rfl | rfl⟩
  · exact up m k
  · have := up (m + -(k : ℤ) * (((n : ℤ) + 1) * n)) k
    rw [show m + -(k : ℤ) * (((n : ℤ) + 1) * n) + (k : ℤ) * (((n : ℤ) + 1) * n) = m by ring]
      at this
    exact this.symm

/-- **Reduction to residues.** If `MS(n, wA r)` is AC-trivial for every `r ∈ [0, n(n+1))`,
then `MS(n, wA m)` is AC-trivial for every `m ∈ ℤ`. -/
theorem MS_wA_of_residues (n : ℕ) (hn : 0 < n)
    (h : ∀ r : ℤ, 0 ≤ r → r < ((n : ℤ) + 1) * n → Reachable (MS n (wA r)) (standard 2))
    (m : ℤ) : Reachable (MS n (wA m)) (standard 2) := by
  set N : ℤ := ((n : ℤ) + 1) * n
  have hN : 0 < N := by positivity
  have := MS_wA_period_mul n m (-(m / N))
  have hr := h (m % N) (Int.emod_nonneg _ hN.ne') (Int.emod_lt_of_pos _ hN)
  rw [show m + -(m / N) * N = m % N by rw [Int.emod_def]; ring] at this
  exact this.trans' hr

end AC
