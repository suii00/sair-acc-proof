import ACProof.AK
import ACProof.ConjugationTrace

/-!
# An S₄ certificate for the conjugation cost of AK(1)

Number the points 0, 1, 2, 3. The generator images are the cycles
(0 2 1 3) and (0 1 3 2). The AK(1) relators map to (2 3) and the identity.
After at most one conjugation the two relators lie in a subgroup generated
by two transpositions. Their two edges disconnect the four points, whereas
the image of the first standard generator acts transitively.
-/

namespace AC
namespace AK1Certificate

abbrev P := Equiv.Perm (Fin 4)

def X : P := Equiv.swap 0 3 * Equiv.swap 0 1 * Equiv.swap 0 2
def Y : P := Equiv.swap 0 2 * Equiv.swap 0 3 * Equiv.swap 0 1
abbrev t : P := Equiv.swap 2 3
def evalWord : Word 2 →* P := FreeGroup.lift ![X, Y]

theorem evalX : evalWord gx = X := by simp [evalWord, gx]
theorem evalY : evalWord gy = Y := by simp [evalWord, gy]

private def two : Subgroup P where
  carrier := {g | g = 1 ∨ g = t}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by
    rintro a (rfl | rfl) <;> simp

/-- The three blocks are {0}, {1}, and {0,1}. -/
private def color (b : Fin 3) (i : Fin 4) : Bool :=
  if b = 0 then decide (i = 0) else if b = 1 then decide (i = 1) else decide (i < 2)

private abbrev preserves (b : Fin 3) (g : P) : Prop := ∀ i, color b (g i) = color b i

private def block (b : Fin 3) : Subgroup P where
  carrier := {g | preserves b g}
  one_mem' := fun _ => rfl
  mul_mem' := fun {g h} hg hh i => (hg (h i)).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

private theorem two_le_block (b : Fin 3) : two ≤ block b := by
  have ht : ∀ k : Fin 3, preserves k t := by decide
  intro g hg
  rcases (show g = 1 ∨ g = t from hg) with rfl | rfl
  · exact (block b).one_mem
  · exact ht b

private theorem conjugate_preserves_block (g : P) : ∃ b : Fin 3, g * t * g⁻¹ ∈ block b := by
  have choose : ∀ i j : Fin 4, ∃ b : Fin 3, preserves b (Equiv.swap i j) := by decide
  obtain ⟨b, hb⟩ := choose (g 2) (g 3)
  refine ⟨b, ?_⟩
  change g * Equiv.swap 2 3 * g⁻¹ ∈ block b
  rw [← Equiv.swap_apply_apply]
  exact hb

private theorem excludesX : ∀ b : Fin 3, ¬preserves b X := by decide

private abbrev mapsInto (R : Relators 2) (K : Subgroup P) : Prop := ∀ i, evalWord (R i) ∈ K

private theorem initial : mapsInto (AK 1) two := by
  intro i
  fin_cases i
  · right
    simp [AK, evalX, evalY]
    decide
  · left
    simp [AK, evalX, evalY]
    decide

private theorem updateInto {R : Relators 2} {K : Subgroup P} (h : mapsInto R K)
    (i : Fin 2) (w : Word 2) (hw : evalWord w ∈ K) : mapsInto (Function.update R i w) K := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using hw
  · simpa [Function.update_of_ne hj] using h j

private theorem freeStep {R : Relators 2} {K : Subgroup P} (h : mapsInto R K)
    (m : PrimitiveMove 2) (hz : m.conjCost = 0) : mapsInto (m.apply R) K := by
  cases m with
  | inv i => exact updateInto h i _ (by simpa using K.inv_mem (h i))
  | mulRight i j _ => exact updateInto h i _ (by simpa using K.mul_mem (h i) (h j))
  | conj i w => cases hz

private theorem freeRun (ms : List (PrimitiveMove 2)) {R : Relators 2} {K : Subgroup P}
    (hr : mapsInto R K) (hz : conjCount ms = 0) : mapsInto (runMoves R ms) K := by
  induction ms generalizing R with
  | nil => exact hr
  | cons m ms ih =>
    change m.conjCost + conjCount ms = 0 at hz
    exact ih (freeStep hr m (by omega)) (by omega)

private theorem oneRun (ms : List (PrimitiveMove 2)) {R : Relators 2}
    (hr : mapsInto R two) (hc : conjCount ms ≤ 1) : ∃ b, mapsInto (runMoves R ms) (block b) := by
  induction ms generalizing R with
  | nil => exact ⟨0, fun i => two_le_block 0 (hr i)⟩
  | cons m ms ih =>
    cases m with
    | inv i =>
      exact ih (freeStep hr (.inv i) rfl) (by simpa [conjCount, PrimitiveMove.conjCost] using hc)
    | mulRight i j hij =>
      exact ih (freeStep hr (.mulRight i j hij) rfl)
        (by simpa [conjCount, PrimitiveMove.conjCost] using hc)
    | conj i w =>
      change 1 + conjCount ms ≤ 1 at hc
      obtain ⟨b, hb⟩ := conjugate_preserves_block (evalWord w)
      refine ⟨b, freeRun ms (updateInto (fun j => two_le_block b (hr j)) i _ ?_) (by omega)⟩
      rcases (show evalWord (R i) = 1 ∨ evalWord (R i) = t from hr i) with h | h
      · simp [map_mul, h]
      · simpa [map_mul, h] using hb

/-- In the four-point permutation image, one conjugation cannot reach the standard pair. -/
theorem lower (ms : List (PrimitiveMove 2)) (h : runMoves (AK 1) ms = standard 2) :
    2 ≤ conjCount ms := by
  by_contra! hl
  obtain ⟨b, hb⟩ := oneRun ms initial (by omega)
  rw [h] at hb
  have hx := hb 0
  change evalWord gx ∈ block b at hx
  rw [evalX] at hx
  exact excludesX b hx

end AK1Certificate

theorem AK1_conjCount_lower (ms : List (PrimitiveMove 2)) (h : runMoves (AK 1) ms = standard 2) :
    2 ≤ conjCount ms := AK1Certificate.lower ms h

end AC
