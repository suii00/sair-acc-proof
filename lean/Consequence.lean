import AC
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Multiplying a relator by consequences of another relator

All statements use the official `AC.Step` / `AC.Reachable` unchanged.
-/

namespace AC
open Function

variable {n : ℕ}

theorem Reachable.single {R S : Relators n} (h : Step R S) : Reachable R S :=
  Relation.ReflTransGen.single h

theorem Reachable.trans' {R S T : Relators n} (h₁ : Reachable R S) (h₂ : Reachable S T) :
    Reachable R T := Relation.ReflTransGen.trans h₁ h₂

/-- Replace relator `i` by `w * R i * w⁻¹` (a single official step). -/
theorem reach_conj (R : Relators n) (i : Fin n) (w : Word n) :
    Reachable R (update R i (w * R i * w⁻¹)) := Reachable.single (Step.conj R i w)

theorem reach_inv (R : Relators n) (i : Fin n) :
    Reachable R (update R i (R i)⁻¹) := Reachable.single (Step.inv R i)

theorem reach_mulRight (R : Relators n) {i j : Fin n} (h : i ≠ j) :
    Reachable R (update R i (R i * R j)) := Reachable.single (Step.mulRight R i j h)

/-- Multiplying relator `i` on the right by a conjugate `c * R j * c⁻¹`. -/
theorem reach_mul_conj (R : Relators n) {i j : Fin n} (h : i ≠ j) (c : Word n) :
    Reachable R (update R i (R i * (c * R j * c⁻¹))) := by
  have h1 := reach_conj R i c⁻¹
  set R1 := update R i (c⁻¹ * R i * c⁻¹⁻¹) with hR1
  have h2 := reach_mulRight R1 h
  set R2 := update R1 i (R1 i * R1 j) with hR2
  have h3 := reach_conj R2 i c
  have e : update R2 i (c * R2 i * c⁻¹) = update R i (R i * (c * R j * c⁻¹)) := by
    simp only [hR2, hR1, update_idem, update_self, update_of_ne h.symm]
    congr 1; group
  exact (h1.trans' h2).trans' (e ▸ h3)

/-- Multiplying relator `i` on the right by a conjugate `c * (R j)⁻¹ * c⁻¹`. -/
theorem reach_mul_conj_inv (R : Relators n) {i j : Fin n} (h : i ≠ j) (c : Word n) :
    Reachable R (update R i (R i * (c * (R j)⁻¹ * c⁻¹))) := by
  have h1 := reach_conj R i c⁻¹
  set R1 := update R i (c⁻¹ * R i * c⁻¹⁻¹) with hR1
  have h2 := reach_inv R1 i
  set R2 := update R1 i (R1 i)⁻¹ with hR2
  have h3 := reach_mulRight R2 h
  set R3 := update R2 i (R2 i * R2 j) with hR3
  have h4 := reach_inv R3 i
  set R4 := update R3 i (R3 i)⁻¹ with hR4
  have h5 := reach_conj R4 i (c * R j)
  have e : update R4 i ((c * R j) * R4 i * (c * R j)⁻¹)
      = update R i (R i * (c * (R j)⁻¹ * c⁻¹)) := by
    simp only [hR4, hR3, hR2, hR1, update_idem, update_self, update_of_ne h.symm]
    congr 1; group
  exact (((h1.trans' h2).trans' h3).trans' h4).trans' (e ▸ h5)

/-- **Consequence lemma.** For `i ≠ j`, relator `i` may be multiplied on the right by
any element of the normal closure (in the free group) of relator `j`. -/
theorem reach_mul_normalClosure (R : Relators n) {i j : Fin n} (h : i ≠ j)
    {w : Word n} (hw : w ∈ Subgroup.normalClosure ({R j} : Set (Word n))) :
    Reachable R (update R i (R i * w)) := by
  -- strengthen: for every value `X` of slot `i`
  suffices H : ∀ X : Word n, Reachable (update R i X) (update R i (X * w)) by
    simpa using H (R i)
  rw [Subgroup.normalClosure] at hw
  induction hw using Subgroup.closure_induction'' with
  | mem x hx =>
    intro X
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    subst ha
    have := reach_mul_conj (update R i X) h c
    simpa [update_idem, update_of_ne h.symm] using this
  | inv_mem x hx =>
    intro X
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    subst ha
    have := reach_mul_conj_inv (update R i X) h c
    have e : (c * R j * c⁻¹)⁻¹ = c * (R j)⁻¹ * c⁻¹ := by group
    rw [e]
    simpa [update_idem, update_of_ne h.symm] using this
  | one => intro X; simpa using Relation.ReflTransGen.refl
  | mul x y _ _ hx hy =>
    intro X
    have h2 := hy (X * x)
    rw [mul_assoc] at h2
    exact (hx X).trans' (by simpa [update_idem] using h2)
