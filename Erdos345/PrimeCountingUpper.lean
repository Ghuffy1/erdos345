import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos345

theorem log_two_profile_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 3 / 4 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

theorem primeCounting_le_five_mul_div_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ 5 * (n : ℝ) / Real.log (n : ℝ) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlogroot := Real.log_sqrt hn0
  have hlog4 : Real.log (4 : ℝ) ≤ 3 / 2 := by
    have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [heq]
    linarith [log_two_profile_bounds.2]
  have hsqrtlog : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 2 * (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hsqpos
    have hsquare := Real.sq_sqrt hn0
    nlinarith [mul_le_mul_of_nonneg_right h hsqpos.le]
  have hp := Chebyshev.pi_le_log4_mul_div (x := (n : ℝ)) hnR
  simp only [Nat.floor_natCast] at hp
  have heq : Real.log 4 * (n : ℝ) / Real.log (Real.sqrt (n : ℝ)) =
      (2 * Real.log 4 * (n : ℝ)) / Real.log (n : ℝ) := by
    rw [hlogroot]
    ring
  rw [heq] at hp
  have hsub : (Nat.primeCounting n : ℝ) - Real.sqrt (n : ℝ) ≤
      (2 * Real.log 4 * (n : ℝ)) / Real.log (n : ℝ) := by linarith
  have hscaled := (le_div_iff₀ hlog).mp hsub
  apply (le_div_iff₀ hlog).mpr
  nlinarith [mul_le_mul_of_nonneg_right hlog4 hn0]

end Erdos345
