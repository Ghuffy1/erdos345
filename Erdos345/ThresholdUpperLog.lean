import Erdos345.GoodDegreeThreshold
import Erdos345.SamplingRatio

namespace Erdos345

theorem log_threshold_envelope_le (k : ℕ) (hk : 0 < k) :
    Real.log ((256 * (fourierN k) ^ (k + 1) : ℕ) : ℝ) ≤
      512 * (k : ℝ) * logScale k ^ 8 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hA : 1 ≤ logScale k ^ 8 := one_le_pow₀ (logScale_ge_one k hk)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hA0 : 0 ≤ logScale k ^ 8 := by positivity
  have hN : (0 : ℝ) < fourierN k := by exact_mod_cast fourierN_pos k
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have hlog := log_fourierN_le k
  have hterm := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by positivity)
  have h256 : Real.log (256 : ℝ) ≤ 255 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 256)
    norm_num at h ⊢
    exact h
  have ha := mul_le_mul_of_nonneg_left hA hk0
  have hb := mul_le_mul_of_nonneg_right hk1 hA0
  push_cast at hterm ⊢
  nlinarith

theorem logScale_mono {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) : logScale j ≤ logScale k := by
  unfold logScale
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < ((2 * j : ℕ) : ℝ))
    (by exact_mod_cast (show 2 * j ≤ 2 * k by omega) : ((2 * j : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ))
  linarith

theorem log_threshold_envelope_le_at_larger {j k : ℕ} (hk : 0 < k) (hkj : k ≤ j) :
    Real.log ((256 * (fourierN k) ^ (k + 1) : ℕ) : ℝ) ≤
      512 * (j : ℝ) * logScale j ^ 8 := by
  apply (log_threshold_envelope_le k hk).trans
  have hlog := logScale_mono hk hkj
  have hp : logScale k ^ 8 ≤ logScale j ^ 8 :=
    pow_le_pow_left₀ (by have := logScale_ge_one k hk; linarith) hlog 8
  apply mul_le_mul _ hp (by positivity) (by positivity)
  have h : (k : ℝ) ≤ j := by exact_mod_cast hkj
  linarith

end Erdos345
