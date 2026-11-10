import Erdos345.PowerWindowGeometry

namespace Erdos345

theorem unit_rpow_tangent (x p : ℝ) (hx : 0 < x) (hx1 : x < 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : x ^ p ≤ 1 - p * (1 - x) := by
  have hs := (Real.concaveOn_rpow hp0 hp1).le_slope_of_hasDerivAt hx.le (by norm_num) hx1
    (Real.hasDerivAt_rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0)))
  simp only [Real.one_rpow, mul_one, slope_def_field] at hs
  have hm := (le_div_iff₀ (sub_pos.mpr hx1)).mp hs
  linarith

/-- An explicit reserve-endpoint bound, uniform for every degree at
least twenty. The rational cubic comparison avoids an asymptotic
expansion of the root. -/
theorem quarter_root_le_one_sub_inv (k : ℕ) (hk : 20 ≤ k) :
    (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) ≤ 1 - (k : ℝ)⁻¹ := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  let p := (k : ℝ)⁻¹
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hp20 : p ≤ 1 / 20 := by
    dsimp only [p]
    exact (inv_le_comm₀ hk0 (by norm_num)).mpr (by simpa only [one_div, inv_inv] using hkR)
  have hp1 : p ≤ 1 := by linarith
  have hb : (1 / 4 : ℝ) ≤ (13 / 20 : ℝ) ^ 3 := by norm_num
  have hroot := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hb hp0
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 13 / 20)] at hroot
  have ht := unit_rpow_tangent (13 / 20) p (by norm_num) (by norm_num) hp0 hp1
  have ht3 := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) ht 3
  have hp2 : p ^ 2 ≤ p / 20 := by
    have hm := mul_le_mul_of_nonneg_left hp20 hp0
    nlinarith only [hm]
  have hp3 : 0 ≤ p ^ 3 := pow_nonneg hp0 _
  have hb3 : (1 - p * (1 - 13 / 20)) ^ 3 ≤ 1 - p := by
    nlinarith only [hp0, hp2, hp3]
  exact hroot.trans (ht3.trans hb3)

end Erdos345
