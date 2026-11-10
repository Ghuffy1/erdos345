import Erdos345.SampledSpanProbability
import Erdos345.ExponentialDomination
import Erdos345.FourierParameters

namespace Erdos345

open Filter

theorem degree_le_fourierN (k : ℕ) : k ≤ fourierN k := by
  by_cases hk : k = 0
  · simp only [hk, Nat.zero_le]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    have hK : 1 ≤ logScale k := logScale_ge_one k hk0
    have hp : logScale k ≤ logScale k ^ 8 := by
      simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ 8 by decide)
    have h := (degree_le_exp_logScale k hk0).trans
      ((Real.exp_le_exp.mpr hp).trans (fourierN_bounds k).1)
    exact_mod_cast h

theorem eventually_span_failure_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (8192 : ℝ) * (k : ℝ) ^ 2 / fourierN k < ε := by
  filter_upwards [eventually_monomial_exp_dominated 2 0 0 (16384 / ε) (by positivity)] with k hk
  simp only [pow_zero, zero_mul, Real.exp_zero, mul_one] at hk
  have hA : 0 ≤ logScale k ^ 8 := by positivity
  have hdom : (16384 / ε) * (k : ℝ) ^ 2 ≤ fourierN k :=
    hk.trans ((Real.exp_le_exp.mpr (by linarith : logScale k ^ 8 / 4 ≤ logScale k ^ 8)).trans
      (fourierN_bounds k).1)
  have hm := mul_le_mul_of_nonneg_right hdom hε.le
  have heq : (16384 / ε) * (k : ℝ) ^ 2 * ε = 16384 * (k : ℝ) ^ 2 := by
    field_simp
  rw [heq] at hm
  have hN : (0 : ℝ) < fourierN k := by exact_mod_cast fourierN_pos k
  have hh : (8192 : ℝ) * (k : ℝ) ^ 2 / fourierN k ≤ ε / 2 := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  exact hh.trans_lt (by linarith)

end Erdos345
