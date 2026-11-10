import Erdos345.RadialUnitCircle
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Erdos345

open Finset

theorem unit_radial_factor_ne_zero (z : ℂ) (hz : ‖z‖ = 1) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) : 1 - (r : ℂ) * z ≠ 0 := by
  intro h
  have heq := congrArg norm (sub_eq_zero.mp h)
  simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, hz, mul_one] at heq
  linarith

theorem unit_radial_log_hasSum (z : ℂ) (hz : ‖z‖ = 1) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℕ => (r ^ m / (m : ℝ)) * (z ^ m).re)
      (-Real.log ‖1 - (r : ℂ) * z‖) := by
  have hnorm : ‖(r : ℂ) * z‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, hz, mul_one] using hr1
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hnorm)
  convert h using 1
  · funext m
    rw [mul_pow, ← Complex.ofReal_pow]
    change _ = (((r ^ m : ℝ) : ℂ) * z ^ m / ((m : ℝ) : ℂ)).re
    rw [Complex.div_ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [Complex.neg_re, Complex.log_re]

theorem log_radialFlatProduct (N : ℕ) (w : ℕ → ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.log ‖radialFlatProduct N w r z‖ =
      ∑ i ∈ range N, (w i : ℝ) * Real.log ‖1 - (r : ℂ) * z ^ (i + 1)‖ := by
  rw [radialFlatProduct_norm, Real.log_prod]
  · apply sum_congr rfl
    intro i _
    exact Real.log_pow _ _
  · intro i _
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr
      (unit_radial_factor_ne_zero (z ^ (i + 1)) (by simp only [norm_pow, hz, one_pow]) r hr hr1))

theorem radialFlatProduct_log_hasSum (N : ℕ) (w : ℕ → ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℕ => (r ^ m / (m : ℝ)) *
      ∑ i ∈ range N, (w i : ℝ) * (z ^ ((i + 1) * m)).re)
      (-Real.log ‖radialFlatProduct N w r z‖) := by
  have hsum := hasSum_sum (s := range N) (f := fun i m : ℕ =>
    (w i : ℝ) * ((r ^ m / (m : ℝ)) * ((z ^ (i + 1)) ^ m).re))
    (fun i _ => (unit_radial_log_hasSum (z ^ (i + 1))
      (by simp only [norm_pow, hz, one_pow]) r hr hr1).mul_left (w i : ℝ))
  convert hsum using 1
  · funext m
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [← pow_mul]
    ring
  · rw [log_radialFlatProduct N w z hz r hr hr1, ← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    ring

end Erdos345
