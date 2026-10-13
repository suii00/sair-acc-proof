import ACProof.Consequence
import Mathlib

/-!
# Basic structural lemmas over the official `AC.Step` / `AC.Reachable`

* invariance of the normal closure and of `PresentsTrivialGroup` under `Reachable`;
* symmetry of `Reachable`;
* left multiplication, swapping two relators, arbitrary relator permutations;
* transport along free-group endomorphisms (e.g. relabelling generators).
-/

namespace AC
open Function

variable {n : ℕ}

/-- The normal closure of the relators. -/
abbrev ncl (R : Relators n) : Subgroup (Word n) := Subgroup.normalClosure (Set.range R)

theorem mem_ncl (R : Relators n) (k : Fin n) : R k ∈ ncl R :=
  Subgroup.subset_normalClosure ⟨k, rfl⟩

theorem ncl_le_of {R S : Relators n} (h : ∀ k, S k ∈ ncl R) : ncl S ≤ ncl R :=
  Subgroup.normalClosure_le_normal (by rintro _ ⟨k, rfl⟩; exact h k)

theorem Step.ncl_eq {R S : Relators n} (h : Step R S) : ncl R = ncl S := by
  cases h with
  | inv i =>
    apply le_antisymm
    · apply ncl_le_of; intro k
      by_cases hk : k = i
      · subst hk; simpa using Subgroup.inv_mem _ (mem_ncl (update R k (R k)⁻¹) k)
      · simpa [update_of_ne hk] using mem_ncl (update R i (R i)⁻¹) k
    · apply ncl_le_of; intro k
      by_cases hk : k = i
      · subst hk; simpa using Subgroup.inv_mem _ (mem_ncl R k)
      · simpa [update_of_ne hk] using mem_ncl R k
  | mulRight i j hij =>
    apply le_antisymm
    · apply ncl_le_of; intro k
      set S := update R i (R i * R j)
      have hj : S j = R j := update_of_ne (Ne.symm hij) _ _
      by_cases hk : k = i
      · subst hk
        have : R k = S k * (S j)⁻¹ := by simp [S, hj]
        rw [this]; exact Subgroup.mul_mem _ (mem_ncl S k) (Subgroup.inv_mem _ (mem_ncl S j))
      · simpa [S, update_of_ne hk] using mem_ncl S k
    · apply ncl_le_of; intro k
      by_cases hk : k = i
      · subst hk; simpa using Subgroup.mul_mem _ (mem_ncl R k) (mem_ncl R j)
      · simpa [update_of_ne hk] using mem_ncl R k
  | conj i w =>
    apply le_antisymm
    · apply ncl_le_of; intro k
      set S := update R i (w * R i * w⁻¹)
      by_cases hk : k = i
      · subst hk
        have : R k = w⁻¹ * S k * w⁻¹⁻¹ := by simp [S]; group
        rw [this]; exact Subgroup.normalClosure_normal.conj_mem _ (mem_ncl S k) _
      · simpa [S, update_of_ne hk] using mem_ncl S k
    · apply ncl_le_of; intro k
      by_cases hk : k = i
      · subst hk; simpa using Subgroup.normalClosure_normal.conj_mem _ (mem_ncl R k) w
      · simpa [update_of_ne hk] using mem_ncl R k

theorem Reachable.ncl_eq {R S : Relators n} (h : Reachable R S) : ncl R = ncl S := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans hs.ncl_eq

/-- **Invariance.** AC-reachability preserves presenting the trivial group. -/
theorem Reachable.presentsTrivialGroup_iff {R S : Relators n} (h : Reachable R S) :
    PresentsTrivialGroup R ↔ PresentsTrivialGroup S := by
  unfold PresentsTrivialGroup PresentedGroup
  rw [show Subgroup.normalClosure (Set.range R) = Subgroup.normalClosure (Set.range S)
    from h.ncl_eq]

theorem presentsTrivialGroup_standard (n : ℕ) : PresentsTrivialGroup (standard n) := by
  unfold PresentsTrivialGroup PresentedGroup
  have : Subgroup.normalClosure (Set.range (standard n)) = ⊤ := by
    rw [eq_top_iff, ← FreeGroup.closure_range_of, Subgroup.closure_le]
    exact Subgroup.subset_normalClosure
  rw [this]
  exact QuotientGroup.subsingleton_quotient_top

/-- Every reachable-to-standard presentation presents the trivial group. -/
theorem Reachable.presentsTrivialGroup {R : Relators n} (h : Reachable R (standard n)) :
    PresentsTrivialGroup R := h.presentsTrivialGroup_iff.mpr (presentsTrivialGroup_standard n)

/-! ## Symmetry -/

theorem Step.reverse {R S : Relators n} (h : Step R S) : Reachable S R := by
  cases h with
  | inv i =>
    have := reach_inv (update R i (R i)⁻¹) i
    simpa [update_idem] using this
  | mulRight i j hij =>
    have hc := reach_mul_normalClosure (update R i (R i * R j)) hij (w := (R j)⁻¹)
      (Subgroup.inv_mem _ (Subgroup.subset_normalClosure (by
        simp [update_of_ne (Ne.symm hij)])))
    simpa [update_idem] using hc
  | conj i w =>
    have := reach_conj (update R i (w * R i * w⁻¹)) i w⁻¹
    have e : w⁻¹ * (w * R i * w⁻¹) * w⁻¹⁻¹ = R i := by group
    simp only [update_idem, update_self, e, update_eq_self] at this
    exact this

theorem Reachable.symm {R S : Relators n} (h : Reachable R S) : Reachable S R := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact hs.reverse.trans' ih

/-! ## Left multiplication and swaps -/

/-- Conjugates of `r` and `r⁻¹` lie in the normal closure of `{r}`. -/
theorem conj_mem_ncl1 {G : Type*} [Group G] (r c : G) :
    c * r * c⁻¹ ∈ Subgroup.normalClosure ({r} : Set G) :=
  (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem r
    (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

theorem conj_inv_mem_ncl1 {G : Type*} [Group G] (r c : G) :
    c * r⁻¹ * c⁻¹ ∈ Subgroup.normalClosure ({r} : Set G) :=
  (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem r⁻¹
    (Subgroup.inv_mem _ (Subgroup.subset_normalClosure (Set.mem_singleton _))) c

/-- Left multiplication: `R i ↦ R j * R i`. -/
theorem reach_mulLeft (R : Relators n) {i j : Fin n} (h : i ≠ j) :
    Reachable R (update R i (R j * R i)) := by
  have hm : (R i)⁻¹ * R j * (R i)⁻¹⁻¹ ∈ Subgroup.normalClosure ({R j} : Set (Word n)) :=
    conj_mem_ncl1 _ _
  have := reach_mul_normalClosure R h hm
  have e : R i * ((R i)⁻¹ * R j * (R i)⁻¹⁻¹) = R j * R i := by group
  rwa [e] at this

/-- Left multiplication by an inverse: `R i ↦ (R j)⁻¹ * R i`. -/
theorem reach_mulLeft_inv (R : Relators n) {i j : Fin n} (h : i ≠ j) :
    Reachable R (update R i ((R j)⁻¹ * R i)) := by
  have hm : (R i)⁻¹ * (R j)⁻¹ * (R i)⁻¹⁻¹ ∈ Subgroup.normalClosure ({R j} : Set (Word n)) :=
    conj_inv_mem_ncl1 _ _
  have := reach_mul_normalClosure R h hm
  have e : R i * ((R i)⁻¹ * (R j)⁻¹ * (R i)⁻¹⁻¹) = (R j)⁻¹ * R i := by group
  rwa [e] at this

/-- Right multiplication by an inverse: `R i ↦ R i * (R j)⁻¹`. -/
theorem reach_mulRight_inv (R : Relators n) {i j : Fin n} (h : i ≠ j) :
    Reachable R (update R i (R i * (R j)⁻¹)) :=
  reach_mul_normalClosure R h (Subgroup.inv_mem _ (Subgroup.subset_normalClosure rfl))

/-- **Swap.** Exchanging two relators is AC-reachable. -/
theorem reach_swap (R : Relators n) (i j : Fin n) :
    Reachable R (R ∘ Equiv.swap i j) := by
  by_cases hij : i = j
  · subst hij; simpa using Relation.ReflTransGen.refl
  -- [a,b] → [ab,b] → [ab,a⁻¹] → [b,a⁻¹] → [b,a]
  set a := R i; set b := R j
  have s1 := reach_mulRight R hij
  set R1 := update R i (R i * R j)
  have hR1i : R1 i = a * b := by simp [R1, a, b]
  have hR1j : R1 j = b := by simp [R1, b, update_of_ne (Ne.symm hij)]
  have s2 := reach_mul_normalClosure R1 (Ne.symm hij) (w := (R1 i)⁻¹)
    (Subgroup.inv_mem _ (Subgroup.subset_normalClosure rfl))
  set R2 := update R1 j (R1 j * (R1 i)⁻¹)
  have hR2i : R2 i = a * b := by simp [R2, update_of_ne hij, hR1i]
  have hR2j : R2 j = a⁻¹ := by simp [R2, hR1i, hR1j]
  have hm : b⁻¹ * R2 j * b⁻¹⁻¹ ∈ Subgroup.normalClosure ({R2 j} : Set (Word n)) :=
    conj_mem_ncl1 _ _
  have s3 := reach_mul_normalClosure R2 hij hm
  set R3 := update R2 i (R2 i * (b⁻¹ * R2 j * b⁻¹⁻¹))
  have hR3i : R3 i = b := by simp [R3, hR2i, hR2j]; group
  have hR3j : R3 j = a⁻¹ := by simp [R3, update_of_ne (Ne.symm hij), hR2j]
  have s4 := reach_inv R3 j
  have e : update R3 j (R3 j)⁻¹ = R ∘ Equiv.swap i j := by
    funext k
    by_cases hkj : k = j
    · subst hkj; simp [hR3j, a]
    by_cases hki : k = i
    · subst hki; simp [update_of_ne hkj, hR3i, b]
    simp only [update_of_ne hkj, comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
    simp [R3, R2, R1, update_of_ne hki, update_of_ne hkj]
  exact s1.trans' (s2.trans' (s3.trans' (e ▸ s4)))

/-- **Permutations.** Any permutation of the relators is AC-reachable. -/
theorem reach_perm (R : Relators n) (σ : Equiv.Perm (Fin n)) : Reachable R (R ∘ σ) := by
  induction σ using Equiv.Perm.swap_induction_on generalizing R with
  | one => simpa using Relation.ReflTransGen.refl
  | swap_mul f x y _ ih =>
    have h1 := reach_swap R x y
    have h2 := ih (R ∘ Equiv.swap x y)
    simpa [comp_assoc, Equiv.Perm.coe_mul] using h1.trans' h2

/-! ## Transport along free-group endomorphisms -/

theorem Step.map (φ : Word n →* Word n) {R S : Relators n} (h : Step R S) :
    Step (φ ∘ R) (φ ∘ S) := by
  cases h with
  | inv i => simpa [comp_update] using Step.inv (φ ∘ R) i
  | mulRight i j hij => simpa [comp_update] using Step.mulRight (φ ∘ R) i j hij
  | conj i w => simpa [comp_update] using Step.conj (φ ∘ R) i (φ w)

theorem Reachable.map (φ : Word n →* Word n) {R S : Relators n} (h : Reachable R S) :
    Reachable (φ ∘ R) (φ ∘ S) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.trans' (Reachable.single (hs.map φ))

/-- Relabelling generators by a permutation `σ` preserves AC-triviality. -/
theorem Reachable.relabel (σ : Equiv.Perm (Fin n)) {R : Relators n}
    (h : Reachable R (standard n)) :
    Reachable (FreeGroup.map σ ∘ R) (standard n) := by
  have h1 := h.map (FreeGroup.map σ)
  have e : FreeGroup.map σ ∘ standard n = standard n ∘ σ := by
    funext k; simp [standard]
  rw [e] at h1
  have h2 := reach_perm (standard n ∘ σ) σ.symm
  simpa [comp_assoc] using h1.trans' h2

end AC
