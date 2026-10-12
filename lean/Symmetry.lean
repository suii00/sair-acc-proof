import ACProof.N4

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

end AC

namespace AC

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

end AC
