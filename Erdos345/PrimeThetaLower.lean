import Erdos345.PrimeCountingUpper

namespace Erdos345

theorem log_le_sqrt_large {x : ℝ} (hx : 16384 ≤ x) :
    Real.log x ≤ (49 / 640 : ℝ) * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs2 := Real.sq_sqrt hx0.le
  have hs : 128 ≤ Real.sqrt x := by nlinarith
  have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    norm_num
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < Real.sqrt x / 128 by positivity)
  rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by norm_num), Real.log_sqrt hx0.le, h128] at hl
  have hlog2 : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith [Real.log_two_lt_d9]
  linarith

theorem log_succ_le_twice_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (x + 1) ≤ 2 * Real.sqrt x := by
  have hs0 := Real.sqrt_nonneg x
  have hs1 := Real.sqrt_nonneg (x + 1)
  have hs2 := Real.sq_sqrt hx
  have hs3 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hs : Real.sqrt (x + 1) ≤ Real.sqrt x + 1 := by nlinarith
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show 0 < x + 1 by linarith))
  rw [Real.log_sqrt (show 0 ≤ x + 1 by linarith)] at hl
  linarith

theorem prime_theta_half_large (n : ℕ) (hn : 16384 ≤ n) :
    (n : ℝ) / 2 ≤ Chebyshev.theta n := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  have hs2 := Real.sq_sqrt hn0
  have hs : 128 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hlog := log_le_sqrt_large hnR
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * Real.sqrt (n : ℝ) by positivity)
  have hlogsucc := log_succ_le_twice_sqrt hn0
  have hl2 : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmain := mul_le_mul_of_nonneg_left hl2 hn0
  have htheta := Chebyshev.theta_ge n
  nlinarith

end Erdos345
