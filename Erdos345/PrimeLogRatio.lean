import Erdos345.PrimePhaseLogBins

namespace Erdos345

theorem prime_log_ratio (p A : ℕ) (hp : 2 ≤ p) (hpA : p ≤ A) :
    (p : ℝ) * Real.log (A : ℝ) ≤ 2 * (A : ℝ) * Real.log (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hpa : (p : ℝ) ≤ A := by exact_mod_cast hpA
  have hlogp : (1 / 2 : ℝ) ≤ Real.log (p : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ p by exact_mod_cast hp)
    linarith [log_two_profile_bounds.1]
  have h := Real.log_le_sub_one_of_pos (div_pos hA0 hp0)
  rw [Real.log_div hA0.ne' hp0.ne'] at h
  have hm := mul_le_mul_of_nonneg_right h hp0.le
  have heq : ((A : ℝ) / p - 1) * p = (A : ℝ) - p := by field_simp
  rw [heq] at hm
  have hcross := mul_nonneg (sub_nonneg.mpr hpa)
    (show 0 ≤ 2 * Real.log (p : ℝ) - 1 by linarith)
  have hpLog : 0 ≤ (p : ℝ) * Real.log (p : ℝ) := mul_nonneg hp0.le (by linarith)
  nlinarith

theorem sum_prime_log_ratio (P : Finset ℕ) (A : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hbound : ∀ p ∈ P, p ≤ A) :
    (∑ p ∈ P, (p : ℝ)) * Real.log (A : ℝ) ≤
      2 * (A : ℝ) * (∑ p ∈ P, Real.log (p : ℝ)) := by
  have h := Finset.sum_le_sum (fun p hp => prime_log_ratio p A (hprime p hp).two_le (hbound p hp))
  simpa only [Finset.sum_mul, Finset.mul_sum] using h

theorem sum_prime_weights_of_phaseBin (P : Finset ℕ) (A : ℕ) (y : ℝ) (j : ℕ)
    (hA : 2 ≤ A) (hy : 1 / 2 < y) (hprime : ∀ p ∈ P, p.Prime)
    (hbound : ∀ p ∈ P, p ≤ A) (hpy : ∀ p ∈ P, (p : ℝ) < y)
    (hbin : ∀ p ∈ P, primePhaseBin y p = j) :
    (∑ p ∈ P, (p : ℝ)) ≤ 4 * (A : ℝ) * Real.log (2 * y) / Real.log (A : ℝ) := by
  have hr := sum_prime_log_ratio P A hprime hbound
  have hb := mul_le_mul_of_nonneg_left (sum_prime_logs_of_phaseBin P y j hy hprime hpy hbin)
    (show 0 ≤ 2 * (A : ℝ) by positivity)
  have hlog : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  apply (le_div_iff₀ hlog).mpr
  nlinarith

end Erdos345
