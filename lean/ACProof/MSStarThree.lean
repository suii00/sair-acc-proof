import ACProof.MSStarConjugations
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! # Three markings for the conjugation cost of MS(n,y⁻¹xyx⁻¹)

In a product of S₃, the dihedral group of a (2n+1)-gon, and S₃,
count one point in each factor where the two relators do not
commute. A single conjugation can gain a point only if both relators in that
marking are odd. The three sign markings restrict to the three nonzero linear
forms on the two-dimensional binary exponent space. Thus at most one marking
can gain a point in a single conjugation. -/

namespace AC
namespace MSStarThree

private abbrev P := Equiv.Perm (Fin 3)
private abbrev G (m : ℕ) := P × DihedralGroup m × P

variable {m : ℕ}
private abbrev Bits := Bool × Bool × Bool
private def oddSign (g : P) : Bool := decide (g.sign = -1)
open DihedralGroup
private def reflected {m : ℕ} : DihedralGroup m → Bool | .r _ => false | .sr _ => true
private def active {G : Type*} [Group G] [DecidableEq G] (g h : G) : ℕ := if g*h = h*g then 0 else 1
private def both (b c : Bool) : ℕ := if b && c then 1 else 0
private theorem inv_active {G : Type*} [Group G] [DecidableEq G] (a b : G) :
    active a⁻¹ b = active a b := by
  have h : a⁻¹*b = b*a⁻¹ ↔ a*b = b*a := by
    change Commute a⁻¹ b ↔ Commute a b
    exact Commute.inv_left_iff
  simp [active,h]
private theorem mul_active {G : Type*} [Group G] [DecidableEq G] (a b : G) :
    active (a*b) b = active a b := by
  simp [active, ← mul_assoc]
private theorem swap_active {G : Type*} [Group G] [DecidableEq G] (a b : G) :
    active a b = active b a := by by_cases h : a*b=b*a <;> simp_all [active, eq_comm]
private theorem dihedral_rules {m : ℕ} (a b : DihedralGroup m) :
    reflected (a*b) = xor (reflected a) (reflected b) ∧
    reflected a⁻¹ = reflected a ∧ active a⁻¹ b = active a b ∧ active (a*b) b = active a b ∧
    active a b = active b a := by
  refine ⟨?_, ?_, inv_active a b, mul_active a b, swap_active a b⟩
  · cases a <;> cases b <;> rfl
  · cases a <;> rfl
private theorem dihedral_conj {m : ℕ} (a b w : DihedralGroup m) :
    reflected (w*a*w⁻¹) = reflected a ∧
    active (w*a*w⁻¹) b ≤ active a b + both (reflected a) (reflected b) := by
  constructor
  · cases a <;> cases w <;> rfl
  · cases a <;> cases b <;> cases w <;>
      simp [active, both, reflected, add_comm] <;> split_ifs <;> try omega
    all_goals
      rename_i ha hb
      exfalso
      apply ha
      first | linear_combination hb | linear_combination - hb
private theorem permutation_rules : ∀ a b : P,
    oddSign (a*b) = xor (oddSign a) (oddSign b) ∧
    oddSign a⁻¹ = oddSign a ∧
    active a⁻¹ b = active a b ∧ active (a*b) b = active a b ∧
    active a b = active b a := by decide

private theorem conjugation_rule : ∀ a b w : P,
    oddSign (w*a*w⁻¹) = oddSign a ∧
    active (w*a*w⁻¹) b ≤ active a b + both (oddSign a) (oddSign b) := by decide

private def flags (g : G m) : Bits := (oddSign g.1, reflected g.2.1, oddSign g.2.2)
private def total (g h : G m) : ℕ := active g.1 h.1 + active g.2.1 h.2.1 + active g.2.2 h.2.2
private def addBits (a b : Bits) : Bits := (xor a.1 b.1, xor a.2.1 b.2.1, xor a.2.2 b.2.2)
private def nonzeroEven (a : Bits) : Bool :=
  a == (false,true,true) || a == (true,false,true) || a == (true,true,false)
private def basis (a b : Bits) : Bool := nonzeroEven a && nonzeroEven b && a != b
private def overlap (a b : Bits) : ℕ := both a.1 b.1 + both a.2.1 b.2.1 + both a.2.2 b.2.2

private theorem binary_rules : ∀ a b : Bits, basis a b = true →
    basis b a = true ∧ basis (addBits a b) b = true ∧ basis a (addBits b a) = true ∧
    overlap a b = 1 := by decide

private theorem flags_inv (a : G m) : flags a⁻¹ = flags a := by
  simp [flags, (fun p => (permutation_rules p p).2.1), (fun (p : DihedralGroup m) => (dihedral_rules p p).2.1)]

private theorem flags_mul (a b : G m) : flags (a*b) = addBits (flags a) (flags b) := by
  simp [flags, addBits, (fun p q => (permutation_rules p q).1), (fun (p q : DihedralGroup m) => (dihedral_rules p q).1)]

private theorem flags_conj (w a : G m) : flags (w*a*w⁻¹) = flags a := by
  simp [flags, (fun p q => (conjugation_rule p p q).1), (fun (p q : DihedralGroup m) => (dihedral_conj p p q).1)]

private theorem total_swap (a b : G m) : total a b = total b a := by
  unfold total
  rw [(permutation_rules a.1 b.1).2.2.2.2, (dihedral_rules a.2.1 b.2.1).2.2.2.2,
    (permutation_rules a.2.2 b.2.2).2.2.2.2]

private theorem total_inv (a b : G m) : total a⁻¹ b = total a b := by
  simp [total, inv_active]

private theorem total_mul (a b : G m) : total (a*b) b = total a b := by
  simp [total, mul_active]

private theorem total_conj (w a b : G m) (h : basis (flags a) (flags b) = true) :
    total (w*a*w⁻¹) b ≤ total a b + 1 := by
  have h₁ := (conjugation_rule a.1 b.1 w.1).2
  have h₂ := (dihedral_conj a.2.1 b.2.1 w.2.1).2
  have h₃ := (conjugation_rule a.2.2 b.2.2 w.2.2).2
  have ho := (binary_rules _ _ h).2.2.2
  dsimp [overlap, flags] at ho
  dsimp [total]
  omega

private abbrev transposition : P := Equiv.swap 0 1
private abbrev cycle : P := Equiv.swap 0 2 * Equiv.swap 0 1
private def x (m : ℕ) : G m := (transposition, sr 0, cycle)
private def y (m : ℕ) : G m := (Equiv.swap 1 2, r 1, transposition)
private def φ (m : ℕ) : Word 2 →* G m := FreeGroup.lift ![x m, y m]
private theorem eval_x : φ m gx = x m := by simp [φ, gx]
private theorem eval_y : φ m gy = y m := by simp [φ, gy]

private def frame (m : ℕ) (R : Relators 2) : Bool := basis (flags (φ m (R 0))) (flags (φ m (R 1)))
private def score (m : ℕ) (R : Relators 2) : ℕ := total (φ m (R 0)) (φ m (R 1))

private theorem step_bound (R : Relators 2) (op : PrimitiveMove 2) (h : frame m R = true) :
    frame m (op.apply R) = true ∧ score m (op.apply R) ≤ score m R + op.conjCost := by
  have hbits := binary_rules _ _ h
  cases op with
  | inv i =>
    fin_cases i
    · simpa [frame, score, PrimitiveMove.apply, PrimitiveMove.conjCost, flags_inv, total_inv]
        using h
    · have hr (a b : G m) : total a b⁻¹ = total a b := by
        rw [total_swap a, total_inv, total_swap]
      simpa [frame, score, PrimitiveMove.apply, PrimitiveMove.conjCost, flags_inv, hr] using h
  | mulRight i j hij =>
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [frame, score, PrimitiveMove.apply, PrimitiveMove.conjCost, flags_mul, total_mul]
        using hbits.2.1
    · have hr (a b : G m) : total a (b*a) = total a b := by
        rw [total_swap, total_mul, total_swap]
      simpa [frame, score, PrimitiveMove.apply, PrimitiveMove.conjCost, flags_mul, hr]
        using hbits.2.2.1
    · exact (hij rfl).elim
  | conj i w =>
    fin_cases i
    · simpa [frame, score, PrimitiveMove.apply, PrimitiveMove.conjCost, flags_conj] using
        And.intro h (total_conj (φ m w) _ _ h)
    · have h' := total_conj (φ m w) _ _ hbits.1
      rw [total_swap, total_swap (φ m (R 1))] at h'
      simpa [frame, score, PrimitiveMove.apply, PrimitiveMove.conjCost, flags_conj] using
        And.intro h h'

private theorem run_bound (R : Relators 2) (ms : List (PrimitiveMove 2)) (h : frame m R = true) :
    score m (runMoves R ms) ≤ score m R + conjCount ms := by
  induction ms generalizing R with
  | nil => simp [runMoves, conjCount]
  | cons op ms ih =>
    obtain ⟨hf, hb⟩ := step_bound R op h
    have ht := ih (op.apply R) hf
    change score m (runMoves (op.apply R) ms) ≤ score m R + (op.conjCost + conjCount ms)
    omega


private abbrev leftY : P := Equiv.swap 1 2
private def relA (n : ℕ) (a b : P) : P := a⁻¹ * b^n * a * (b^(n+1))⁻¹
private def relB (a b : P) : P := a * (b⁻¹*a*b*a⁻¹)⁻¹

private theorem first_image (n : ℕ) : φ (2*n+1) (MS n wstar 0) =
    (relA n transposition leftY, 1, relA n cycle transposition) := by
  have zero_mod : (2 * (n : ZMod (2*n+1)) + 1) = 0 := by
    exact_mod_cast ZMod.natCast_self (2*n+1)
  apply Prod.ext
  · simp [MS, eval_x, eval_y, x, y, relA, leftY]
  · apply Prod.ext
    · simp [MS, eval_x, eval_y, x, y, one_def, -r_zero]
      linear_combination -zero_mod
    · simp [MS, eval_x, eval_y, x, y, relA]

private theorem second_image (n : ℕ) : φ (2*n+1) (MS n wstar 1) =
    (relB transposition leftY, sr 2, relB cycle transposition) := by
  simp [MS, wstar, eval_x, eval_y, x, y, relB, leftY]
  ring

private theorem parity_power (a : P) (ha : a^2=1) (n : ℕ) :
    a^n = (if Odd n then a else 1) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [if_neg (Nat.not_odd_iff_even.mpr he)]
    obtain ⟨k, hk⟩ := he
    rw [show n = 2*k by omega, pow_mul, ha, one_pow]
  · rw [if_pos ho]
    obtain ⟨k, hk⟩ := ho
    rw [show n = 2*k+1 by omega, pow_succ, pow_mul, ha, one_pow, one_mul]

/-- The middle marking sends the relators to the identity and a reflection.
The two permutation markings start with total score zero for odd n and one for even n. -/
private theorem initial_even_odd (n : ℕ) :
    frame (2*n+1) (MS n wstar) = true ∧
    score (2*n+1) (MS n wstar) = (if Odd n then 0 else 1) := by
  have ht : transposition ^ 2 = 1 := by decide
  have hy : leftY ^ 2 = 1 := by decide
  have mid : active (1 : DihedralGroup (2*n+1)) (sr 2) = 0 := by simp [active]
  have flagId : reflected (1 : DihedralGroup (2*n+1)) = false := rfl
  unfold frame score
  rw [first_image, second_image]
  have flagSr : reflected (sr 2 : DihedralGroup (2*n+1)) = true := rfl
  simp only [flags, total, mid, flagSr, flagId, Nat.add_zero]
  by_cases ho : Odd n
  · have hn : ¬Odd (n+1) := by rw [Nat.odd_iff] at *; omega
    simp only [relA, parity_power _ ht, parity_power _ hy, if_pos ho, if_neg hn, inv_one, mul_one]
    decide
  · have hn : Odd (n+1) := by rw [Nat.odd_iff] at *; omega
    simp only [relA, parity_power _ ht, parity_power _ hy, if_neg ho, if_pos hn,
      mul_one, inv_mul_cancel, one_mul]
    decide

private theorem final_score {n : ℕ} (hn : 0 < n) : score (2*n+1) (standard 2) = 3 := by
  have h₂ : (2 : ZMod (2*n+1)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 (2*n+1)).mp h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < 2*n+1) hd
  have hm : active (sr 0 : DihedralGroup (2*n+1)) (r 1) = 1 := by
    have h : (1 : ZMod (2*n+1)) ≠ -1 := by
      intro he
      apply h₂
      linear_combination he
    simp [active,h]
  change total (φ (2*n+1) gx) (φ (2*n+1) gy) = 3
  rw [eval_x, eval_y]
  simp only [total, x, y, hm]
  decide

/-- The three parity markings require three conjugations for odd parameters
and two for nonzero even parameters. -/
theorem bounds {n : ℕ} (hn : 0 < n) {ms : List (PrimitiveMove 2)}
    (h : runMoves (MS n wstar) ms = standard 2) :
    (if Odd n then 3 else 2) ≤ conjCount ms := by
  obtain ⟨hf, hs⟩ := initial_even_odd n
  have hrun := run_bound _ ms hf
  rw [h, final_score hn, hs] at hrun
  split_ifs at * <;> omega

theorem lower {ms : List (PrimitiveMove 2)} (h : runMoves (MS 1 wstar) ms = standard 2) :
    3 ≤ conjCount ms := by simpa using bounds (by decide) h

theorem zero_lower {ms : List (PrimitiveMove 2)} (h : runMoves (MS 0 wstar) ms = standard 2) :
    1 ≤ conjCount ms := by
  have he : score 1 (standard 2) = 2 := by
    change total (φ 1 gx) (φ 1 gy) = 2
    rw [eval_x, eval_y]
    decide
  obtain ⟨hf, hs⟩ := initial_even_odd 0
  have ht := run_bound _ ms hf
  simp [h, he, hs] at ht
  omega

end MSStarThree

theorem MSStar_zero_conjCount_exact :
    (∀ ms : List (PrimitiveMove 2), runMoves (MS 0 wstar) ms = standard 2 → 1 ≤ conjCount ms) ∧
    ∃ ms : List (PrimitiveMove 2), runMoves (MS 0 wstar) ms = standard 2 ∧ conjCount ms = 1 :=
  ⟨fun _ h => MSStarThree.zero_lower h, ⟨msStarZeroMoves, MSStar_zero_witness⟩⟩

theorem MSStar_one_conjCount_exact :
    (∀ ms : List (PrimitiveMove 2), runMoves (MS 1 wstar) ms = standard 2 → 3 ≤ conjCount ms) ∧
    ∃ ms : List (PrimitiveMove 2), runMoves (MS 1 wstar) ms = standard 2 ∧ conjCount ms = 3 :=
  ⟨fun _ h => MSStarThree.lower h,
   ⟨msStarOneMoves, MSStar_one_witness.1, MSStar_one_witness.2.1⟩⟩

end AC
