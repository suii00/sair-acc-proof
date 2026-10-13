import ACProof.NewFamilies

/-! # Proof-automation helpers used by the certified search paths (no mathematical content). -/

namespace AC

macro "step_tac3" : tactic =>
  `(tactic| first | rfl | (simp; done) | (simp [sq, mul_assoc]; done) | (simp [pow_succ, mul_assoc]; done) | (simp; group) | group | (simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Function.update, Matrix.head_cons]; group) | (simp; simp only [zpow_neg, zpow_one, zpow_two, pow_two, sq, mul_assoc, mul_inv_rev, inv_inv]; done))

theorem std_xy {a b : FreeGroup (Fin 2)} (ha : a = gx ∨ a = gx⁻¹) (hb : b = gy ∨ b = gy⁻¹) :
    Reachable ![a, b] (standard 2) := by
  have hs : (standard 2) = ![gx, gy] := by apply fin2_ext <;> rfl
  rw [hs]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact reach_of_eq (reach_inv ![gx, gy⁻¹] 1) (by apply fin2_ext <;> simp)
  · exact reach_of_eq (reach_inv ![gx⁻¹, gy] 0) (by apply fin2_ext <;> simp)
  · exact (reach_inv ![gx⁻¹, gy⁻¹] 0).trans' (reach_of_eq (reach_inv _ 1) (by apply fin2_ext <;> simp))

theorem std_yx {a b : FreeGroup (Fin 2)} (ha : a = gx ∨ a = gx⁻¹) (hb : b = gy ∨ b = gy⁻¹) :
    Reachable ![b, a] (standard 2) := by
  refine (reach_perm ![b, a] (Equiv.swap 0 1)).trans' ?_
  have e : (![b, a] ∘ Equiv.swap (0 : Fin 2) 1) = ![a, b] := by
    apply fin2_ext <;> simp
  rw [e]; exact std_xy ha hb

macro "std_fin" : tactic =>
  `(tactic| first | exact std_xy (by first | exact Or.inl rfl | exact Or.inr rfl) (by first | exact Or.inl rfl | exact Or.inr rfl) | exact std_yx (by first | exact Or.inl rfl | exact Or.inr rfl) (by first | exact Or.inl rfl | exact Or.inr rfl))

macro "ms_eq_tac" : tactic =>
  `(tactic| (apply fin2_ext <;> first
    | rfl
    | (simp [MS, pow_succ, mul_assoc]; done)
    | (simp [MS, pow_succ, mul_assoc, zpow_ofNat]; done)
    | (simp [MS]; group)
    | (simp only [MS, Matrix.cons_val_zero, Matrix.cons_val_one]; group)))


end AC
