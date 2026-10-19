import ACProof.NewFamilies

/-!
# Correspondence with the three-parameter Miller–Schupp family of Sneiderman

Sneiderman (github.com/Robby955/ac-square-divisibility, file `lean/ACMillerSchupp.lean`, public since
2026-09-12) studies `presentation n a b c = (x⁻¹yⁿxy^{-(n+1)}, x⁻¹y^a x y^b x⁻¹ y^c)` against the same official
`AC.lean`. We restate that pair here with our own generator names (no import of their code) and prove that
`MS n (wA m)` is AC-equivalent (two official steps each way) to the parameter point `(a,b,c) = (-m, m, 0)`.
This is used only to compare scopes; it is not an alternative definition of anything official.
-/

namespace AC

/-- Sneiderman's `presentation n a b c`, restated with `gx`, `gy`. -/
def SnPres (n : ℕ) (a b c : ℤ) : Relators 2 :=
  ![gx⁻¹ * gy ^ n * gx * gy ^ (-((n : ℤ) + 1)), gx⁻¹ * gy ^ a * gx * gy ^ b * gx⁻¹ * gy ^ c]

theorem MS_wA_reach_SnPres (n : ℕ) (m : ℤ) : Reachable (MS n (wA m)) (SnPres n (-m) m 0) := by
  refine (reach_inv _ 1).trans' (reach_of_conj _ _ 1 gx⁻¹ ?_)
  apply fin2_ext
  · simp only [MS, SnPres, Function.update]; simp; group
  · simp [MS, SnPres, wA, Function.update]; group

theorem SnPres_reach_MS_wA (n : ℕ) (m : ℤ) : Reachable (SnPres n (-m) m 0) (MS n (wA m)) :=
  (MS_wA_reach_SnPres n m).symm

end AC
