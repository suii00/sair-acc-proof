import AC

/-! # Counting conjugations in directed ordinary Andrews–Curtis moves -/

namespace AC

/-- A label for each of the three official operations, including the arbitrary conjugator. -/
inductive PrimitiveMove (n : ℕ) where
  | inv (i : Fin n)
  | mulRight (i j : Fin n) (hij : i ≠ j)
  | conj (i : Fin n) (w : Word n)

def PrimitiveMove.apply {n : ℕ} (m : PrimitiveMove n) (R : Relators n) : Relators n :=
  match m with
  | .inv i => Function.update R i (R i)⁻¹
  | .mulRight i j _ => Function.update R i (R i * R j)
  | .conj i w => Function.update R i (w * R i * w⁻¹)

def PrimitiveMove.conjCost {n : ℕ} : PrimitiveMove n → ℕ
  | .inv _ | .mulRight _ _ _ => 0
  | .conj _ _ => 1

/-- Execute a chronological list of labels starting at a specified tuple. -/
def runMoves {n : ℕ} (R : Relators n) : List (PrimitiveMove n) → Relators n
  | [] => R
  | m :: ms => runMoves (m.apply R) ms

/-- Count every occurrence of the official conjugation operation. -/
def conjCount {n : ℕ} : List (PrimitiveMove n) → ℕ
  | [] => 0
  | m :: ms => m.conjCost + conjCount ms

def PrimitiveMove.mulCost {n : ℕ} : PrimitiveMove n → ℕ
  | .mulRight _ _ _ => 1
  | .inv _ | .conj _ _ => 0

/-- Count the official right multiplications. -/
def mulCount {n : ℕ} : List (PrimitiveMove n) → ℕ
  | [] => 0
  | m :: ms => m.mulCost + mulCount ms

theorem mulCount_append {n : ℕ} (xs ys : List (PrimitiveMove n)) :
    mulCount (xs ++ ys) = mulCount xs + mulCount ys := by
  induction xs with
  | nil => simp [mulCount]
  | cons m ms ih => simp [mulCount, ih, Nat.add_assoc]

theorem runMoves_append {n : ℕ} (R : Relators n) (xs ys : List (PrimitiveMove n)) :
    runMoves R (xs ++ ys) = runMoves (runMoves R xs) ys := by
  induction xs generalizing R with
  | nil => rfl
  | cons m ms ih => exact ih (m.apply R)

theorem conjCount_append {n : ℕ} (xs ys : List (PrimitiveMove n)) :
    conjCount (xs ++ ys) = conjCount xs + conjCount ys := by
  induction xs with
  | nil => simp [conjCount]
  | cons m ms ih => simp [conjCount, ih, Nat.add_assoc]

theorem PrimitiveMove.step {n : ℕ} (m : PrimitiveMove n) (R : Relators n) : Step R (m.apply R) := by
  cases m with
  | inv i => exact Step.inv R i
  | mulRight i j h => exact Step.mulRight R i j h
  | conj i w => exact Step.conj R i w

theorem Step.exists_primitiveMove {n : ℕ} {R S : Relators n} (s : Step R S) :
    ∃ m : PrimitiveMove n, m.apply R = S := by
  cases s with
  | inv i => exact ⟨.inv i, rfl⟩
  | mulRight i j h => exact ⟨.mulRight i j h, rfl⟩
  | conj i w => exact ⟨.conj i w, rfl⟩

theorem runMoves_reachable {n : ℕ} (R : Relators n) (ms : List (PrimitiveMove n)) :
    Reachable R (runMoves R ms) := by
  induction ms generalizing R with
  | nil => exact .refl
  | cons m ms ih => exact Relation.ReflTransGen.head (m.step R) (ih (m.apply R))

theorem reachable_iff_exists_runMoves {n : ℕ} {R S : Relators n} :
    Reachable R S ↔ ∃ ms : List (PrimitiveMove n), runMoves R ms = S := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ s ih =>
      obtain ⟨ms, rfl⟩ := ih
      obtain ⟨m, hm⟩ := s.exists_primitiveMove
      exact ⟨ms ++ [m], (runMoves_append R ms [m]).trans hm⟩
  · rintro ⟨ms, rfl⟩
    exact runMoves_reachable R ms

end AC
