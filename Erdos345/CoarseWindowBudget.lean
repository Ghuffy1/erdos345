import Erdos345.InverseRadiusBudget

namespace Erdos345

theorem log_sixteen_ge_two : (2 : ℝ) ≤ Real.log 16 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
    norm_num
  linarith

theorem coarseWindowScale_conditions (k W : ℕ) (hk : 20 ≤ k) (H : ℝ) (hH : 0 ≤ H)
    (hW : 128000 * (k : ℝ) * (H + 1) ≤ W) :
    1000 * (k : ℝ) ≤ (W : ℝ) / 8 ∧ (258 : ℝ) ≤ (W : ℝ) / 8 ∧
      2 ≤ Real.log (((W : ℝ) / 8) / (1000 * (k : ℝ))) := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hbase : 128000 * (k : ℝ) ≤ W := by nlinarith [mul_nonneg hk0.le hH]
  have hratio : (16 : ℝ) ≤ ((W : ℝ) / 8) / (1000 * (k : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  refine ⟨by linarith, by linarith, ?_⟩
  exact log_sixteen_ge_two.trans (Real.log_le_log (by norm_num) hratio)

theorem coarseWindowFloor_gt (N k W : ℕ) (hk : 20 ≤ k) (H : ℝ) (hH : 0 ≤ H)
    (hWN : W ≤ N) (hW : 128000 * (k : ℝ) * (H + 1) ≤ W) :
    H < windowEnergyFloor N k ((W : ℝ) / 8) := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hWN' : (W : ℝ) ≤ N := by exact_mod_cast hWN
  have hkH : 0 ≤ (k : ℝ) * H := mul_nonneg hk0.le hH
  have hn : H < (N : ℝ) / (512 * (k : ℝ)) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith
  have hw : H < ((W : ℝ) / 8) / (256 * (k : ℝ)) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith
  have hlog := (coarseWindowScale_conditions k W hk H hH hW).2.2
  have hs0 : 0 ≤ ((W : ℝ) / 8) / (256 * (k : ℝ)) := by positivity
  have hm := mul_le_mul_of_nonneg_left (show 1 ≤
      Real.log (((W : ℝ) / 8) / (1000 * (k : ℝ))) - 1 by linarith) hs0
  have hs : H < ((W : ℝ) / 8) / (256 * (k : ℝ)) *
      (Real.log (((W : ℝ) / 8) / (1000 * (k : ℝ))) - 1) := by
    exact hw.trans_le (by simpa only [mul_one] using hm)
  exact lt_min hn hs

theorem coarseWindowRadius_budget (k W : ℕ) (hk : 20 ≤ k) (H : ℝ) (hH : 0 ≤ H)
    (hW : 128000 * (k : ℝ) * (H + 1) ≤ W) :
    16 * ((k + 1 : ℕ) : ℝ) * H ≤ Real.pi * W := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hπW := mul_le_mul_of_nonneg_right Real.two_le_pi (Nat.cast_nonneg (α := ℝ) W)
  have hkH := mul_nonneg hk0 hH
  push_cast
  nlinarith

end Erdos345
