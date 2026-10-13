import ACProof.Consequence
import Mathlib

/-!
# The Miller–Schupp subfamily `MS(n, y^k)` is AC-trivial for all `n : ℕ`, `k : ℤ`

`MS(n, w) = ⟨x, y | x⁻¹ yⁿ x = y^{n+1}, x = w⟩` (Miller–Schupp 1999), encoded with the
official `AC.Relators 2`: generator `0 = x`, `1 = y`, relators
`x⁻¹ yⁿ x y^{-(n+1)}` and `x w⁻¹`.
-/

namespace AC
open Function

/-- generator `x` -/ abbrev gx : Word 2 := FreeGroup.of 0
/-- generator `y` -/ abbrev gy : Word 2 := FreeGroup.of 1

/-- Miller–Schupp presentation `MS(n, w)`. -/
def MS (n : ℕ) (w : Word 2) : Relators 2 :=
  ![gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹, gx * w⁻¹]

theorem reach_of_mul {n : ℕ} (R T : Relators n) {i j : Fin n} (h : i ≠ j) (w : Word n)
    (hw : w ∈ Subgroup.normalClosure ({R j} : Set (Word n)))
    (hT : update R i (R i * w) = T) : Reachable R T :=
  hT ▸ reach_mul_normalClosure R h hw

theorem reach_of_conj {n : ℕ} (R T : Relators n) (i : Fin n) (w : Word n)
    (hT : update R i (w * R i * w⁻¹) = T) : Reachable R T :=
  hT ▸ reach_conj R i w

theorem fin2_ext {R T : Relators 2} (h0 : R 0 = T 0) (h1 : R 1 = T 1) : R = T := by
  funext a; fin_cases a <;> assumption

/-- Substituting `x ↦ y^k`, `y ↦ y`. -/
def substX (k : ℤ) : Word 2 →* Word 2 := FreeGroup.lift ![gy ^ k, gy]

/-- **Substitution theorem.** If a word `r` becomes `y⁻¹` (freely) after substituting
`x := y^k`, then `⟨x, y | r, x y^{-k}⟩` is AC-trivial (official `Reachable`). -/
theorem subst_reachable (r : Word 2) (k : ℤ) (hr : substX k r = gy⁻¹) :
    Reachable ![r, gx * (gy ^ k)⁻¹] (standard 2) := by
  set r1 : Word 2 := gx * (gy ^ k)⁻¹
  have s1 : Reachable ![r, r1] ![gy⁻¹, r1] := by
    refine reach_of_mul _ _ (i := 0) (j := 1) (by decide) (r⁻¹ * gy⁻¹) ?_ ?_
    · show r⁻¹ * gy⁻¹ ∈ Subgroup.normalClosure {r1}
      rw [← QuotientGroup.eq_one_iff]
      have hr1 : (QuotientGroup.mk r1 : Word 2 ⧸ Subgroup.normalClosure {r1}) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
      have hx : (QuotientGroup.mk gx : Word 2 ⧸ Subgroup.normalClosure {r1}) =
          QuotientGroup.mk (gy ^ k) := by
        have := hr1; simp only [r1, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
        exact mul_inv_eq_one.mp this
      have hom : (QuotientGroup.mk' (Subgroup.normalClosure {r1})).comp (substX k) =
          QuotientGroup.mk' _ := by
        ext a; fin_cases a
        · simpa [substX] using hx.symm
        · simp [substX]
      have key := congrArg (fun f => f r) hom
      simp only [MonoidHom.comp_apply, hr, QuotientGroup.mk'_apply] at key
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← key]
      group
    · refine fin2_ext ?_ rfl
      simp
  have s2 : Reachable ![gy⁻¹, r1] ![gy⁻¹, gx] := by
    refine reach_of_mul _ _ (i := 1) (j := 0) (by decide) (gy ^ k) ?_ ?_
    · have h : gy⁻¹ ∈ Subgroup.normalClosure ({gy⁻¹} : Set (Word 2)) :=
        Subgroup.subset_normalClosure rfl
      have := Subgroup.zpow_mem _ h (-k)
      simpa [zpow_neg, inv_zpow'] using this
    · apply fin2_ext <;> simp [r1]
  have s3 : Reachable ![gy⁻¹, gx] ![gy⁻¹ * gx, gx] :=
    reach_of_mul _ _ (i := 0) (j := 1) (by decide) gx
      (Subgroup.subset_normalClosure rfl) (by apply fin2_ext <;> simp)
  have s4 : Reachable ![gy⁻¹ * gx, gx] ![gy⁻¹ * gx, gy] :=
    reach_of_mul _ _ (i := 1) (j := 0) (by decide) (gy⁻¹ * gx)⁻¹
      (Subgroup.inv_mem _ (Subgroup.subset_normalClosure rfl))
      (by apply fin2_ext <;> simp)
  have s5 : Reachable ![gy⁻¹ * gx, gy] ![gx * gy⁻¹, gy] :=
    reach_of_conj _ _ 0 gy (by apply fin2_ext <;> simp)
  have s6 : Reachable ![gx * gy⁻¹, gy] (standard 2) :=
    reach_of_mul _ _ (i := 0) (j := 1) (by decide) gy
      (Subgroup.subset_normalClosure rfl)
      (by apply fin2_ext <;> simp [standard])
  exact s1.trans' (s2.trans' (s3.trans' (s4.trans' (s5.trans' s6))))

/-- **Corollary.** For every `n : ℕ` and `k : ℤ`, `MS(n, y^k)` is AC-trivial. -/
theorem MS_ypow_reachable (n : ℕ) (k : ℤ) : Reachable (MS n (gy ^ k)) (standard 2) := by
  apply subst_reachable
  simp [substX]
  group

end AC
