import ACProof.AK

/-!
# Two parametric subfamilies of `MS(n, y^{-m} x y^m x⁻¹)` (search-then-certify, round 3)

`wA m = y^{-m} x y^m x⁻¹` (`m = 1` is Shehper et al.'s `w⋆`, Theorem B(ii)).
* `MS_wA_neg  n` : `MS(n, wA (-n))`   is AC-trivial, all `n`.
* `MS_wA_succ n` : `MS(n, wA (n+1))`  is AC-trivial, all `n`.
Both reduce, modulo the first relator, to `MS(n, y^{∓1})`.
-/

namespace AC

abbrev wA (m : ℤ) : Word 2 := gy ^ (-m) * gx * gy ^ m * gx⁻¹

/-- In `F / ⟨⟨x⁻¹yⁿx y^{-(n+1)}⟩⟩`: `Yⁿ X = X Y^{n+1}`. -/
theorem K_rel (n : ℕ) :
    (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure
        ({gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹} : Set (Word 2))) ^ (n : ℤ) *
      QuotientGroup.mk gx =
      QuotientGroup.mk gx * (QuotientGroup.mk gy) ^ ((n : ℤ) + 1) := by
  set N := Subgroup.normalClosure ({gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹} : Set (Word 2))
  have hr : (QuotientGroup.mk (gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹) : Word 2 ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow] at hr
  have h2 := mul_inv_eq_one.mp hr
  have h3 : (QuotientGroup.mk gx : Word 2 ⧸ N)⁻¹ * (QuotientGroup.mk gy) ^ (n : ℤ) *
      QuotientGroup.mk gx = (QuotientGroup.mk gy) ^ ((n : ℤ) + 1) := by
    simpa [← zpow_natCast] using h2
  calc (QuotientGroup.mk gy : Word 2 ⧸ N) ^ (n : ℤ) * QuotientGroup.mk gx
      = QuotientGroup.mk gx * ((QuotientGroup.mk gx)⁻¹ * (QuotientGroup.mk gy) ^ (n : ℤ) *
          QuotientGroup.mk gx) := by group
    _ = _ := by rw [h3]

/-- **New family (m = -n).** `MS(n, yⁿ x y^{-n} x⁻¹)` is AC-trivial for every `n`. -/
theorem MS_wA_neg (n : ℕ) : Reachable (MS n (wA (-(n : ℤ)))) (standard 2) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  set r1 : Word 2 := gx * (wA (-(n : ℤ)))⁻¹
  have K := K_rel n
  have s1 : Reachable (MS n (wA (-(n : ℤ)))) ![r0, gx⁻¹ * r1 * gx⁻¹⁻¹] :=
    reach_slot1_conj r0 r1 gx⁻¹
  have s2 : Reachable ![r0, gx⁻¹ * r1 * gx⁻¹⁻¹] (MS n (gy ^ (1 : ℤ))) := by
    apply reach_slot1_mod
    simp only [r1, wA, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    set X := (QuotientGroup.mk gx : Word 2 ⧸ Subgroup.normalClosure {r0})
    set Y := (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure {r0})
    calc X⁻¹ * (X * (Y ^ (-(-(n : ℤ))) * X * Y ^ (-(n : ℤ)) * X⁻¹)⁻¹) * X⁻¹⁻¹
        = X * Y ^ (n : ℤ) * (Y ^ (n : ℤ) * X)⁻¹ * X := by group
      _ = X * Y ^ (n : ℤ) * (X * Y ^ ((n : ℤ) + 1))⁻¹ * X := by rw [K]
      _ = X * (Y ^ (1 : ℤ))⁻¹ := by group
  exact s1.trans' (s2.trans' (MS_ypow_reachable n 1))

/-- **New family (m = n+1).** `MS(n, y^{-(n+1)} x y^{n+1} x⁻¹)` is AC-trivial for every `n`. -/
theorem MS_wA_succ (n : ℕ) : Reachable (MS n (wA ((n : ℤ) + 1))) (standard 2) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  have K := K_rel n
  have s1 : Reachable (MS n (wA ((n : ℤ) + 1))) (MS n (gy ^ (-1 : ℤ))) := by
    apply reach_slot1_mod
    simp only [wA, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    set X := (QuotientGroup.mk gx : Word 2 ⧸ Subgroup.normalClosure {r0})
    set Y := (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure {r0})
    calc X * (Y ^ (-((n : ℤ) + 1)) * X * Y ^ ((n : ℤ) + 1) * X⁻¹)⁻¹
        = X * X * (X * Y ^ ((n : ℤ) + 1))⁻¹ * Y ^ ((n : ℤ) + 1) := by group
      _ = X * X * (Y ^ (n : ℤ) * X)⁻¹ * Y ^ ((n : ℤ) + 1) := by rw [K]
      _ = X * (Y ^ (-1 : ℤ))⁻¹ := by group
  exact s1.trans' (MS_ypow_reachable n (-1))

/-- **New family (m = -(n+1)).** `MS(n, y^{n+1} x y^{-(n+1)} x⁻¹)` is AC-trivial for every `n`. -/
theorem MS_wA_negsucc (n : ℕ) : Reachable (MS n (wA (-((n : ℤ) + 1)))) (standard 2) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  have K := K_rel n
  have s1 : Reachable (MS n (wA (-((n : ℤ) + 1)))) (MS n (gy ^ (1 : ℤ))) := by
    apply reach_slot1_mod
    simp only [wA, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    set X := (QuotientGroup.mk gx : Word 2 ⧸ Subgroup.normalClosure {r0})
    set Y := (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure {r0})
    calc X * (Y ^ (-(-((n : ℤ) + 1))) * X * Y ^ (-((n : ℤ) + 1)) * X⁻¹)⁻¹
        = X * X * (Y * (Y ^ (n : ℤ) * X) * Y ^ (-((n : ℤ) + 1)))⁻¹ := by group
      _ = X * X * (Y * (X * Y ^ ((n : ℤ) + 1)) * Y ^ (-((n : ℤ) + 1)))⁻¹ := by rw [K]
      _ = X * (Y ^ (1 : ℤ))⁻¹ := by group
  exact s1.trans' (MS_ypow_reachable n 1)

/-- **New family (m = n).** `MS(n, y^{-n} x yⁿ x⁻¹)` is AC-trivial for every `n`. -/
theorem MS_wA_self (n : ℕ) : Reachable (MS n (wA (n : ℤ))) (standard 2) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  set r1 : Word 2 := gx * (wA (n : ℤ))⁻¹
  have K := K_rel n
  have s1 : Reachable (MS n (wA (n : ℤ))) ![r0, gx⁻¹ * r1 * gx⁻¹⁻¹] :=
    reach_slot1_conj r0 r1 gx⁻¹
  have s2 : Reachable ![r0, gx⁻¹ * r1 * gx⁻¹⁻¹] (MS n (gy ^ (-1 : ℤ))) := by
    apply reach_slot1_mod
    simp only [r1, wA, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    set X := (QuotientGroup.mk gx : Word 2 ⧸ Subgroup.normalClosure {r0})
    set Y := (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure {r0})
    calc X⁻¹ * (X * (Y ^ (-(n : ℤ)) * X * Y ^ (n : ℤ) * X⁻¹)⁻¹) * X⁻¹⁻¹
        = X * (Y ^ (-(n : ℤ)) * (X * Y ^ ((n : ℤ) + 1)) * Y⁻¹)⁻¹ * X := by group
      _ = X * (Y ^ (-(n : ℤ)) * (Y ^ (n : ℤ) * X) * Y⁻¹)⁻¹ * X := by rw [K]
      _ = X * (Y ^ (-1 : ℤ))⁻¹ := by group
  exact s1.trans' (s2.trans' (MS_ypow_reachable n (-1)))

section Mult
variable {Q : Type*} [Group Q] {X Y : Q}

theorem conj_mult_nat (n : ℕ) (hK : Y ^ (n : ℤ) * X = X * Y ^ ((n : ℤ) + 1)) (q : ℕ) :
    Y ^ (-((q : ℤ) * n)) * X * Y ^ ((q : ℤ) * n) = X * Y ^ (-(q : ℤ)) := by
  have L1 : Y ^ (-(n : ℤ)) * X * Y ^ (n : ℤ) = X * Y⁻¹ := by
    calc Y ^ (-(n : ℤ)) * X * Y ^ (n : ℤ)
        = Y ^ (-(n : ℤ)) * (X * Y ^ ((n : ℤ) + 1)) * Y⁻¹ := by group
      _ = Y ^ (-(n : ℤ)) * (Y ^ (n : ℤ) * X) * Y⁻¹ := by rw [hK]
      _ = X * Y⁻¹ := by group
  induction q with
  | zero => simp
  | succ q ih =>
    calc Y ^ (-(((q + 1 : ℕ) : ℤ) * n)) * X * Y ^ (((q + 1 : ℕ) : ℤ) * n)
        = Y ^ (-(n : ℤ)) * (Y ^ (-((q : ℤ) * n)) * X * Y ^ ((q : ℤ) * n)) * Y ^ (n : ℤ) := by
          push_cast; group
      _ = (Y ^ (-(n : ℤ)) * X * Y ^ (n : ℤ)) * Y ^ (-(q : ℤ)) := by rw [ih]; group
      _ = X * Y ^ (-((q + 1 : ℕ) : ℤ)) := by rw [L1]; push_cast; group

theorem conj_mult (n : ℕ) (hK : Y ^ (n : ℤ) * X = X * Y ^ ((n : ℤ) + 1)) (q : ℤ) :
    Y ^ (-(q * n)) * X * Y ^ (q * n) = X * Y ^ (-q) := by
  rcases Int.eq_nat_or_neg q with ⟨k, rfl | rfl⟩
  · exact conj_mult_nat n hK k
  · have h := conj_mult_nat n hK k
    have e : X = Y ^ ((k : ℤ) * n) * (X * Y ^ (-(k : ℤ))) * Y ^ (-((k : ℤ) * n)) := by
      rw [← h]; group
    calc Y ^ (-(-(k : ℤ) * n)) * X * Y ^ (-(k : ℤ) * n)
        = Y ^ ((k : ℤ) * n) * (X * Y ^ (-(k : ℤ))) * Y ^ (-((k : ℤ) * n)) * Y ^ (k : ℤ) := by
          group
      _ = X * Y ^ (k : ℤ) := by rw [← e]
      _ = X * Y ^ (-(-(k : ℤ))) := by rw [neg_neg]
end Mult

/-- **New family (m = q·n).** For every `n : ℕ` and `q : ℤ`, `MS(n, y^{-qn} x y^{qn} x⁻¹)`
is AC-trivial. -/
theorem MS_wA_mult (n : ℕ) (q : ℤ) : Reachable (MS n (wA (q * n))) (standard 2) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  set r1 : Word 2 := gx * (wA (q * n))⁻¹
  have K := K_rel n
  have s1 : Reachable (MS n (wA (q * n))) ![r0, gx⁻¹ * r1 * gx⁻¹⁻¹] :=
    reach_slot1_conj r0 r1 gx⁻¹
  have s2 : Reachable ![r0, gx⁻¹ * r1 * gx⁻¹⁻¹] (MS n (gy ^ (-q))) := by
    apply reach_slot1_mod
    simp only [r1, wA, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
    set X := (QuotientGroup.mk gx : Word 2 ⧸ Subgroup.normalClosure {r0})
    set Y := (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure {r0})
    have C := conj_mult n K q
    calc X⁻¹ * (X * (Y ^ (-(q * n)) * X * Y ^ (q * n) * X⁻¹)⁻¹) * X⁻¹⁻¹
        = X * (Y ^ (-(q * n)) * X * Y ^ (q * n))⁻¹ * X := by group
      _ = X * (X * Y ^ (-q))⁻¹ * X := by rw [C]
      _ = X * (Y ^ (-q))⁻¹ := by group
  exact s1.trans' (s2.trans' (MS_ypow_reachable n (-q)))

/-- **Reduction mod n.** `MS(n, wA(q·n + j))` reaches `MS(n, y^{-j} x y^{j-q} x⁻¹)`,
for all `n : ℕ`, `q j : ℤ`. -/
theorem MS_wA_reduce (n : ℕ) (q j : ℤ) :
    Reachable (MS n (wA (q * n + j))) (MS n (gy ^ (-j) * gx * gy ^ (j - q) * gx⁻¹)) := by
  set r0 : Word 2 := gx⁻¹ * gy ^ n * gx * (gy ^ (n + 1))⁻¹
  have K := K_rel n
  apply reach_slot1_mod
  simp only [wA, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  set X := (QuotientGroup.mk gx : Word 2 ⧸ Subgroup.normalClosure {r0})
  set Y := (QuotientGroup.mk gy : Word 2 ⧸ Subgroup.normalClosure {r0})
  have C := conj_mult n K q
  calc X * (Y ^ (-(q * n + j)) * X * Y ^ (q * n + j) * X⁻¹)⁻¹
      = X * (Y ^ (-j) * (Y ^ (-(q * n)) * X * Y ^ (q * n)) * Y ^ j * X⁻¹)⁻¹ := by group
    _ = X * (Y ^ (-j) * (X * Y ^ (-q)) * Y ^ j * X⁻¹)⁻¹ := by rw [C]
    _ = X * (Y ^ (-j) * X * Y ^ (j - q) * X⁻¹)⁻¹ := by group

/-- **Summary.** For every `n` and every `m ∈ nℤ ∪ {n+1, -(n+1)}`, `MS(n, wA m)` is AC-trivial. -/
theorem MS_wA_diag (n : ℕ) (m : ℤ)
    (hm : (∃ q : ℤ, m = q * n) ∨ m = (n : ℤ) + 1 ∨ m = -((n : ℤ) + 1)) :
    Reachable (MS n (wA m)) (standard 2) := by
  rcases hm with ⟨q, rfl⟩ | rfl | rfl
  · exact MS_wA_mult n q
  · exact MS_wA_succ n
  · exact MS_wA_negsucc n

end AC
