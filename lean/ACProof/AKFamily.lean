import ACProof.General

/-!
# An Andrews–Curtis path to the Akbulut–Kirby presentation

For every natural `n`, reducing the parameter `m = -(2n+1)` gives the same
word `y x y x⁻¹`. Conjugating the second relator identifies the resulting
presentation with `MS n (wk 0)`.
-/

namespace AC

/-- The negative representative has an ordinary AC path to `AK n`. -/
theorem MS_wA_reach_AK (n : ℕ) :
    Reachable (MS n (wA (-(2 * (n : ℤ) + 1)))) (AK n) := by
  have h := MS_wA_reduce n (-2) (-1)
  rw [show (-2 : ℤ) * n + (-1) = -(2 * (n : ℤ) + 1) by ring] at h
  have reduced : Reachable (MS n (wA (-(2 * (n : ℤ) + 1)))) (MS n (gy * gx * gy * gx⁻¹)) := by
    simpa only [show -(-1 : ℤ) = 1 by decide, show (-1 : ℤ) - (-2) = 1 by decide,
      zpow_one] using h
  let r₀ : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  have conjugated := reach_slot1_conj r₀ (gx * (gy * gx * gy * gx⁻¹)⁻¹) gx⁻¹
  have e : gx⁻¹ * (gx * (gy * gx * gy * gx⁻¹)⁻¹) * (gx⁻¹)⁻¹ = gx * (wk 0)⁻¹ := by
    simp only [wk, neg_zero, zpow_zero, one_mul]
    group
  rw [e] at conjugated
  exact reduced.trans' (conjugated.trans' ((MS_wk_equiv n 0 1).trans' (AK_reach_MS n).symm))

/-- Every period translate of the negative representative reaches `AK n`. -/
theorem MS_wA_period_reach_AK (n : ℕ) (t : ℤ) :
    Reachable (MS n (wA (-(2 * (n : ℤ) + 1) + t * (((n : ℤ) + 1) * n)))) (AK n) :=
  (MS_wA_period_mul n (-(2 * (n : ℤ) + 1)) t).symm.trans' (MS_wA_reach_AK n)

/-- Both signs and their translates have the same AC-triviality as `AK n`. -/
theorem MS_wA_pm_iff_AK (n : ℕ) (m t : ℤ)
    (hm : m = -(2 * (n : ℤ) + 1) + t * (((n : ℤ) + 1) * n) ∨
          m = (2 * (n : ℤ) + 1) + t * (((n : ℤ) + 1) * n)) :
    Reachable (MS n (wA m)) (standard 2) ↔ Reachable (AK n) (standard 2) := by
  rcases hm with h | h
  · have path := MS_wA_period_reach_AK n t
    rw [← h] at path
    exact ⟨fun hs => path.symm.trans' hs, fun hs => path.trans' hs⟩
  · have path := MS_wA_period_reach_AK n (-t)
    have e : -m = -(2 * (n : ℤ) + 1) + -t * (((n : ℤ) + 1) * n) := by rw [h]; ring
    rw [← e] at path
    constructor
    · intro hs
      exact path.symm.trans' (MS_wA_negate n (-m) (by simpa only [neg_neg] using hs))
    · intro hs
      exact MS_wA_negate n m (path.trans' hs)

/-- The residue class 19 modulo 30 reaches the actual `AK 5` presentation. -/
theorem MS5_wA_19_reach_AK5 (m : ℤ) (hm : m % 30 = 19) :
    Reachable (MS 5 (wA m)) (AK 5) := by
  have path := MS_wA_period_reach_AK 5 (m / 30 + 1)
  change Reachable (MS 5 (wA (-11 + (m / 30 + 1) * 30))) (AK 5) at path
  rwa [show -11 + (m / 30 + 1) * 30 = m by omega] at path

/-- At residues 11 and 19 modulo 30, AC-triviality is equivalent to that of `AK 5`. -/
theorem MS5_wA_11_19_iff_AK5 (m : ℤ) (hm : m % 30 = 11 ∨ m % 30 = 19) :
    Reachable (MS 5 (wA m)) (standard 2) ↔ Reachable (AK 5) (standard 2) := by
  rcases hm with h | h
  · apply MS_wA_pm_iff_AK 5 m (m / 30)
    right
    change m = 11 + m / 30 * 30
    omega
  · have path := MS5_wA_19_reach_AK5 m h
    exact ⟨fun hs => path.symm.trans' hs, fun hs => path.trans' hs⟩

-- Period representatives for the previously studied n = 3, 4 and 5 cases.
example : Reachable (MS 3 (wA 5)) (AK 3) := MS_wA_period_reach_AK 3 1
example : Reachable (MS 4 (wA (-9))) (AK 4) := MS_wA_reach_AK 4
example : Reachable (MS 5 (wA (-11))) (AK 5) := MS_wA_reach_AK 5
example : Reachable (MS 5 (wA 11)) (standard 2) ↔ Reachable (AK 5) (standard 2) :=
  MS5_wA_11_19_iff_AK5 11 (Or.inl (by decide))

end AC
