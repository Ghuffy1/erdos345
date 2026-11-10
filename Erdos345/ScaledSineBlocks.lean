import Erdos345.OddSineBlocks

namespace Erdos345

noncomputable def scaledSineBlock (p v : ℕ) (t : ℝ) : ℝ :=
  oddSineSum (p * v) (Real.pi * t / (2 * (p : ℝ)))

theorem scaledSineBlock_abs_le (p v : ℕ) (t : ℝ) :
    |scaledSineBlock p v t| ≤ (p * v : ℕ) := oddSineSum_abs_le _ _

theorem scaledSineBlock_nonneg (p v : ℕ) (hp : 0 < p) {t : ℝ}
    (ht : 0 ≤ t) (htp : t ≤ 2 * (p : ℝ)) : 0 ≤ scaledSineBlock p v t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  apply oddSineSum_nonneg
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p)).mpr
    nlinarith [Real.pi_pos]

theorem scaledSineBlock_small_lower (p v : ℕ) (hp : 0 < p) (hv : 0 < v) {t : ℝ}
    (ht : 0 < t) (hvt : (v : ℝ) * t ≤ 1) :
    2 / Real.pi * (v : ℝ) ^ 2 * p * t ≤ scaledSineBlock p v t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hx : 0 < Real.pi * t / (2 * (p : ℝ)) := by positivity
  have hangle : ((p * v : ℕ) : ℝ) * (Real.pi * t / (2 * (p : ℝ))) =
      Real.pi / 2 * ((v : ℝ) * t) := by
    push_cast
    field_simp
  have hsmall : ((p * v : ℕ) : ℝ) * (Real.pi * t / (2 * (p : ℝ))) ≤ Real.pi / 2 := by
    rw [hangle]
    nlinarith [Real.pi_pos]
  have hM : 1 ≤ p * v := Nat.succ_le_of_lt (Nat.mul_pos hp hv)
  have hb := oddSineSum_small_angle_lower (p * v) hM hx hsmall
  have heq : 4 / Real.pi ^ 2 * ((p * v : ℕ) : ℝ) ^ 2 *
      (Real.pi * t / (2 * (p : ℝ))) = 2 / Real.pi * (v : ℝ) ^ 2 * p * t := by
    push_cast
    field_simp
    ring
  rw [heq] at hb
  exact hb

end Erdos345
