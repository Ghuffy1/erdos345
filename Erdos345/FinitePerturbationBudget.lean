import Erdos345.UnreservedFrequencyBound
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos345

/-- A coarse separation W>=8*X^2 makes the entire power-phase
perturbation term at most eight, uniformly for positive degrees. -/
theorem flat_radius_perturbation_le_eight (k X W : ℕ) (hk : 0 < k) (hX : 0 < X)
    (hW : 0 < W) (H : ℝ)
    (hheight : 16 * ((k + 1 : ℕ) : ℝ) * H ≤ Real.pi * W)
    (hWX : 8 * (X : ℝ) ^ 2 ≤ W) :
    2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ 8 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hbase : (4 : ℝ) * X / W ≤ 1 / (2 * X) := by
    apply (div_le_div_iff₀ hWR (by positivity)).mpr
    nlinarith only [hWX]
  have hbase1 : (4 : ℝ) * X / W ≤ 1 :=
    hbase.trans ((div_le_one (by positivity)).mpr (by linarith))
  have hp : ((4 : ℝ) * X / W) ^ k ≤ 1 / (2 * X) :=
    (pow_le_of_le_one (by positivity) hbase1 (Nat.ne_of_gt hk)).trans hbase
  have hnear : flatInverseRadius k W H * (X : ℝ) ^ k ≤ 1 / (2 * X) := by
    calc
      _ ≤ ((4 : ℝ) / W) ^ k * (X : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (flatInverseRadius_le_power k W hW H hheight) (by positivity)
      _ = ((4 : ℝ) * X / W) ^ k := by rw [← mul_pow]; congr 1; ring
      _ ≤ _ := hp
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (flatInverseRadius_nonneg k W H) (by positivity)) hnear 2
  have hm := mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ 2 * Real.pi ^ 2 * (X : ℝ) by positivity)
  have hcollapse : 2 * Real.pi ^ 2 * (X : ℝ) * (1 / (2 * X)) ^ 2 =
      Real.pi ^ 2 / (2 * X) := by field_simp
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfinal : Real.pi ^ 2 / (2 * X) ≤ 8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  rw [hcollapse] at hm
  nlinarith only [hm, hfinal]

theorem perturbation_budget_of_separation (k X W : ℕ) (hk : 0 < k) (hX : 0 < X)
    (hW : 0 < W) (H E : ℝ)
    (hheight : 16 * ((k + 1 : ℕ) : ℝ) * H ≤ Real.pi * W)
    (hWX : 8 * (X : ℝ) ^ 2 ≤ W) (hmargin : 2 * H + 8 ≤ E) :
    2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ E := by
  have h := flat_radius_perturbation_le_eight k X W hk hX hW H hheight hWX
  linarith

end Erdos345
