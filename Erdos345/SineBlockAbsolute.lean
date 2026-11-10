import Erdos345.ScaledSineBlocks

namespace Erdos345

theorem sum_odd_reals (M : ℕ) :
    (∑ i ∈ Finset.range M, (2 * (i : ℝ) + 1)) = (M : ℝ) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem oddSineSum_abs_le_square_mul (M : ℕ) (x : ℝ) :
    |oddSineSum M x| ≤ (M : ℝ) ^ 2 * |x| := by
  calc
    _ ≤ ∑ i ∈ Finset.range M, |Real.sin ((2 * (i : ℝ) + 1) * x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range M, (2 * (i : ℝ) + 1) * |x| := by
      apply Finset.sum_le_sum
      intro i _
      have h := Real.abs_sin_le_abs (x := (2 * (i : ℝ) + 1) * x)
      simpa only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (i : ℝ) + 1)] using h
    _ = _ := by rw [← Finset.sum_mul, sum_odd_reals]

theorem scaledSineBlock_abs_linear (p v : ℕ) (hp : 0 < p) (t : ℝ) :
    |scaledSineBlock p v t| ≤ Real.pi / 2 * (p : ℝ) * (v : ℝ) ^ 2 * |t| := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hb := oddSineSum_abs_le_square_mul (p * v) (Real.pi * t / (2 * (p : ℝ)))
  change |scaledSineBlock p v t| ≤ _ at hb
  have heq : ((p * v : ℕ) : ℝ) ^ 2 * |Real.pi * t / (2 * (p : ℝ))| =
      Real.pi / 2 * (p : ℝ) * (v : ℝ) ^ 2 * |t| := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (show (0 : ℝ) < 2 * p by positivity)]
    push_cast
    field_simp
  rw [heq] at hb
  exact hb

end Erdos345
