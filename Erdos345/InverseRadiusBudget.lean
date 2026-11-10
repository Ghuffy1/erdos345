import Erdos345.EmptyExceptionalGrid

namespace Erdos345

theorem flatInverseRadius_le_power (k W : ℕ) (hW : 0 < W) (H : ℝ)
    (hbudget : 16 * ((k + 1 : ℕ) : ℝ) * H ≤ Real.pi * W) :
    flatInverseRadius k W H ≤ ((4 : ℝ) / W) ^ k := by
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hs : Real.sqrt (16 * ((k + 1 : ℕ) : ℝ) * H / (Real.pi * W)) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one (by positivity)).mpr hbudget
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (4 : ℝ) ^ k / (W : ℝ) ^ k by positivity)
  simpa only [flatInverseRadius, mul_one, div_pow] using hm

theorem flatInverseRadius_eighth_scale (k W : ℕ) (hW : 0 < W) (H : ℝ)
    (hbudget : 16 * ((k + 1 : ℕ) : ℝ) * H ≤ Real.pi * W) :
    flatInverseRadius k W H * ((W : ℝ) / 8) ^ k ≤ 1 := by
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hW
  calc
    _ ≤ ((4 : ℝ) / W) ^ k * ((W : ℝ) / 8) ^ k :=
      mul_le_mul_of_nonneg_right (flatInverseRadius_le_power k W hW H hbudget) (by positivity)
    _ = (1 / 2 : ℝ) ^ k := by
      rw [← mul_pow]
      congr 1
      field_simp
      norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem flatInverseRadius_le_one (k W : ℕ) (hW : 4 ≤ W) (H : ℝ)
    (hbudget : 16 * ((k + 1 : ℕ) : ℝ) * H ≤ Real.pi * W) :
    flatInverseRadius k W H ≤ 1 := by
  have hW0 : 0 < W := by omega
  have hWR : (4 : ℝ) ≤ W := by exact_mod_cast hW
  have hbase : (4 : ℝ) / W ≤ 1 := (div_le_one (by positivity)).mpr hWR
  exact (flatInverseRadius_le_power k W hW0 H hbudget).trans
    (pow_le_one₀ (by positivity) hbase)

end Erdos345
