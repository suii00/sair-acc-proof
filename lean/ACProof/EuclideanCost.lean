import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace AC

/-- Number of subtractions until one coordinate reaches zero. -/
def euclideanCost (a b : ℕ) : ℕ :=
  if min a b = 0 then 0
  else euclideanCost (min a b) (max a b - min a b) + 1
termination_by a + b
decreasing_by
  rcases le_total a b with h | h
  · simp only [min_eq_left h, max_eq_right h] at *
    omega
  · simp only [min_eq_right h, max_eq_left h] at *
    omega

theorem euclideanCost_comm (a b : ℕ) : euclideanCost a b = euclideanCost b a := by
  rw [euclideanCost.eq_def a b, euclideanCost.eq_def b a, min_comm b a, max_comm b a]

@[simp] theorem euclideanCost_zero_left (b : ℕ) : euclideanCost 0 b = 0 := by
  rw [euclideanCost]
  simp

@[simp] theorem euclideanCost_zero_right (a : ℕ) : euclideanCost a 0 = 0 := by
  rw [euclideanCost_comm, euclideanCost_zero_left]

theorem euclideanCost_add_left (a b : ℕ) (hb : 0 < b) :
    euclideanCost (a + b) b = euclideanCost a b + 1 := by
  have h : b ≤ a + b := by omega
  rw [euclideanCost.eq_def (a + b) b, min_eq_right h, max_eq_left h, if_neg (Nat.ne_of_gt hb),
    Nat.add_sub_cancel, euclideanCost_comm b a]

@[simp] theorem euclideanCost_one_right (a : ℕ) : euclideanCost a 1 = a := by
  induction a with
  | zero => exact euclideanCost_zero_left 1
  | succ a ih => rw [euclideanCost_add_left a 1 (by decide), ih]

private theorem euclideanCost_add_bounds (a b : ℕ) :
    euclideanCost (a + b) b ≤ euclideanCost a b + 1 ∧
    euclideanCost a b ≤ euclideanCost (a + b) b + 1 := by
  by_cases h : b = 0
  · simp [h]
  · rw [euclideanCost_add_left a b (by omega)]
    omega

/-- When the signs differ, the unchanged magnitude can be the sum of the
old and new magnitudes. Both costs then reduce to the same unordered pair. -/
private theorem euclideanCost_complement_bounds (a c : ℕ) :
    euclideanCost c (a + c) ≤ euclideanCost a (a + c) + 1 ∧
    euclideanCost a (a + c) ≤ euclideanCost c (a + c) + 1 := by
  have step (d e : ℕ) :
      euclideanCost d (d + e) = euclideanCost d e + (if d = 0 then 0 else 1) := by
    by_cases hd : d = 0
    · simp [hd]
    · rw [euclideanCost_comm d (d + e), Nat.add_comm d e,
        euclideanCost_add_left e d (by omega), euclideanCost_comm e d, if_neg hd]
  have ha := step a c
  have hc := step c a
  rw [Nat.add_comm c a, euclideanCost_comm c a] at hc
  split_ifs at ha hc <;> omega

/-- Adding one signed coordinate to the other changes the subtraction count by at most one. -/
theorem euclideanCost_mulRight (u v : ℤ) :
    euclideanCost (u + v).natAbs v.natAbs ≤ euclideanCost u.natAbs v.natAbs + 1 ∧
    euclideanCost u.natAbs v.natAbs ≤ euclideanCost (u + v).natAbs v.natAbs + 1 := by
  have triangle : (u + v).natAbs = u.natAbs + v.natAbs ∨
      u.natAbs = (u + v).natAbs + v.natAbs ∨ v.natAbs = u.natAbs + (u + v).natAbs := by
    rcases Int.natAbs_eq u with h | h <;> rcases Int.natAbs_eq v with k | k <;>
      rcases Int.natAbs_eq (u + v) with l | l <;> omega
  rcases triangle with h | h | h
  · rw [h]
    exact euclideanCost_add_bounds _ _
  · have hs := euclideanCost_add_bounds (u + v).natAbs v.natAbs
    rw [← h] at hs
    exact hs.symm
  · rw [h]
    exact euclideanCost_complement_bounds _ _

theorem euclideanCost_add_left_le (u v : ℤ) :
    euclideanCost (u + v).natAbs v.natAbs ≤ euclideanCost u.natAbs v.natAbs + 1 :=
  (euclideanCost_mulRight u v).1

theorem euclideanCost_le_add_left (u v : ℤ) :
    euclideanCost u.natAbs v.natAbs ≤ euclideanCost (u + v).natAbs v.natAbs + 1 :=
  (euclideanCost_mulRight u v).2

theorem euclideanCost_add_right_le (u v : ℤ) :
    euclideanCost u.natAbs (u + v).natAbs ≤ euclideanCost u.natAbs v.natAbs + 1 := by
  rw [euclideanCost_comm u.natAbs (u + v).natAbs, euclideanCost_comm u.natAbs v.natAbs,
    add_comm u v]
  exact euclideanCost_add_left_le v u

theorem euclideanCost_le_add_right (u v : ℤ) :
    euclideanCost u.natAbs v.natAbs ≤ euclideanCost u.natAbs (u + v).natAbs + 1 := by
  rw [euclideanCost_comm u.natAbs (u + v).natAbs, euclideanCost_comm u.natAbs v.natAbs,
    add_comm u v]
  exact euclideanCost_le_add_left v u

end AC
