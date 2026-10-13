import ACProof.Period
import ACProof.Tactics

/-!
# General families of AC-trivial `MS(n, wA m)` (all `n`), independent of the instance files.

* `MS_wA_mult_succ` : `m ∈ (n+1)ℤ`.
* `MS_wA_one`       : `m = 1` (via `w⋆`).
* `MS_wA_negate`    : transfer of AC-triviality from `wA (-m)` to `wA m` (via the automorphism `y ↦ y⁻¹`).
* `MS_wA_neg_one`, `MS_wA_pm_one` : `m ≡ ±1 (mod n(n+1))`.
* `MS_wA_cover`     : `m ∈ nℤ ∪ (n+1)ℤ ∪ (±1 + n(n+1)ℤ)`.
-/

namespace AC

theorem MS_wA_mult_succ (n : ℕ) (q : ℤ) :
    Reachable (MS n (wA (q * ((n : ℤ) + 1)))) (standard 2) := by
  have h := MS_wA_reduce n q q
  rw [show q * (n : ℤ) + q = q * ((n : ℤ) + 1) by ring] at h
  have e : gy ^ (-q) * gx * gy ^ (q - q) * gx⁻¹ = gy ^ (-q) := by group
  rw [e] at h
  exact h.trans' (MS_ypow_reachable n (-q))


theorem MS_wA_one (n : ℕ) : Reachable (MS n (wA 1)) (standard 2) := by
  have e : wA 1 = wstar := by simp [wA, wstar]
  rw [e]; exact MS_wstar_reachable n


end AC
/-!
# The symmetry `y ↦ y⁻¹`: `MS(n, wA m)` and `MS(n, wA (-m))` are simultaneously AC-trivial.

The automorphism `ψ : x ↦ x, y ↦ y⁻¹` sends the first Miller–Schupp relator to a conjugate of its inverse,
and `wA (-m)` to `wA m`. Since `Reachable` is preserved by any endomorphism (`Reachable.map`), a trivialization
of `MS(n, wA (-m))` maps to one of `MS(n, wA m)`.
-/

namespace AC

/-- `ψ : x ↦ x, y ↦ y⁻¹`. -/
def psi : Word 2 →* Word 2 := FreeGroup.lift ![gx, gy⁻¹]

@[simp] lemma psi_gx : psi gx = gx := by simp [psi]
@[simp] lemma psi_gy : psi gy = gy⁻¹ := by simp [psi]

theorem MS_wA_negate (n : ℕ) (m : ℤ) (h : Reachable (MS n (wA (-m))) (standard 2)) :
    Reachable (MS n (wA m)) (standard 2) := by
  have h1 := h.map psi
  have e1 : psi ∘ MS n (wA (-m)) =
      ![gx⁻¹ * gy⁻¹ ^ n * gx * (gy⁻¹ ^ (n + 1))⁻¹, gx * (wA m)⁻¹] := by
    apply fin2_ext
    · simp [MS]
    · simp [MS, wA, inv_zpow']
  have e2 : psi ∘ standard 2 = ![gx, gy⁻¹] := by
    apply fin2_ext <;> simp [standard]
  rw [e1, e2] at h1
  -- from `MS n (wA m)` to `psi ∘ MS n (wA (-m))`: conjugate r0 by y^{-(n+1)} and invert.
  have s1 := reach_slot0_conj (gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹) (gx * (wA m)⁻¹) (gy ^ (n + 1))⁻¹
  have s2 := reach_inv ![(gy ^ (n + 1))⁻¹ * (gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹) * ((gy ^ (n + 1))⁻¹)⁻¹,
    gx * (wA m)⁻¹] 0
  have e3 : Function.update ![(gy ^ (n + 1))⁻¹ * (gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹) * ((gy ^ (n + 1))⁻¹)⁻¹,
      gx * (wA m)⁻¹] 0 (![(gy ^ (n + 1))⁻¹ * (gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹) * ((gy ^ (n + 1))⁻¹)⁻¹,
      gx * (wA m)⁻¹] 0)⁻¹ = ![gx⁻¹ * gy⁻¹ ^ n * gx * (gy⁻¹ ^ (n + 1))⁻¹, gx * (wA m)⁻¹] := by
    apply fin2_ext
    · simp only [Function.update_self, Matrix.cons_val_zero]; simp only [inv_pow]; group
    · rfl
  rw [e3] at s2
  have s3 : Reachable ![gx, gy⁻¹] (standard 2) := std_xy (Or.inl rfl) (Or.inr rfl)
  have e0 : MS n (wA m) = ![gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹, gx * (wA m)⁻¹] := rfl
  rw [e0]
  exact s1.trans' (s2.trans' (h1.trans' s3))


/-- `MS(n, y x y⁻¹ x⁻¹)` (i.e. `wA (-1)`) is AC-trivial for every `n`. -/
theorem MS_wA_neg_one (n : ℕ) : Reachable (MS n (wA (-1))) (standard 2) :=
  MS_wA_negate n (-1) (by simpa using MS_wA_one n)

/-- `MS(n, wA m)` is AC-trivial whenever `m ≡ ±1 (mod n(n+1))`, for every `n`. -/
theorem MS_wA_pm_one (n : ℕ) (t : ℤ) :
    Reachable (MS n (wA (1 + t * (((n : ℤ) + 1) * n)))) (standard 2) ∧
    Reachable (MS n (wA (-1 + t * (((n : ℤ) + 1) * n)))) (standard 2) := by
  constructor
  · have := MS_wA_period_mul n (1 + t * (((n : ℤ) + 1) * n)) (-t)
    rw [show 1 + t * (((n : ℤ) + 1) * n) + -t * (((n : ℤ) + 1) * n) = 1 by ring] at this
    exact this.trans' (MS_wA_one n)
  · have := MS_wA_period_mul n (-1 + t * (((n : ℤ) + 1) * n)) (-t)
    rw [show -1 + t * (((n : ℤ) + 1) * n) + -t * (((n : ℤ) + 1) * n) = -1 by ring] at this
    exact this.trans' (MS_wA_neg_one n)

/-- Union of the general families: `m ∈ nℤ ∪ (n+1)ℤ ∪ (1 + n(n+1)ℤ) ∪ (-1 + n(n+1)ℤ)`. -/
theorem MS_wA_cover (n : ℕ) (m : ℤ)
    (hm : (∃ q : ℤ, m = q * n) ∨ (∃ q : ℤ, m = q * ((n : ℤ) + 1)) ∨
      (∃ t : ℤ, m = 1 + t * (((n : ℤ) + 1) * n)) ∨ (∃ t : ℤ, m = -1 + t * (((n : ℤ) + 1) * n))) :
    Reachable (MS n (wA m)) (standard 2) := by
  rcases hm with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact MS_wA_mult n q
  · exact MS_wA_mult_succ n q
  · exact (MS_wA_pm_one n t).1
  · exact (MS_wA_pm_one n t).2

end AC
