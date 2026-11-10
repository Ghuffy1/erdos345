import Erdos345.QuasipolynomialCenter

namespace Erdos345

open Finset Polynomial

theorem unit_circle_radial_norm (z : ℂ) (hz : ‖z‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) * ‖1 - z‖ ≤ 2 * ‖1 - (r : ℂ) * z‖ := by
  have hcircle : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hz
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have hre : -1 ≤ z.re := by
    have h := (abs_le.mp (by simpa only [hz] using Complex.abs_re_le_norm z)).1
    exact h
  have ha : ‖1 - z‖ ^ 2 = 2 - 2 * z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hb : ‖1 - (r : ℂ) * z‖ ^ 2 = 1 + r ^ 2 - 2 * r * z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h := congrArg (fun x : ℝ => r ^ 2 * x) hcircle
    nlinarith
  have hproduct : 0 ≤ (1 - r) ^ 2 * (1 + z.re) := mul_nonneg (sq_nonneg _) (by linarith)
  have hsquare : ((1 + r) * ‖1 - z‖) ^ 2 ≤ (2 * ‖1 - (r : ℂ) * z‖) ^ 2 := by
    rw [mul_pow, mul_pow, ha, hb]
    nlinarith
  have hleft : 0 ≤ (1 + r) * ‖1 - z‖ := mul_nonneg (by linarith) (norm_nonneg _)
  have hright : 0 ≤ 2 * ‖1 - (r : ℂ) * z‖ := by positivity
  nlinarith

theorem unit_circle_radial_ratio (z : ℂ) (hz : ‖z‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    ‖1 - z‖ ≤ (2 / (1 + r)) * ‖1 - (r : ℂ) * z‖ := by
  have h := unit_circle_radial_norm z hz r hr
  have hp : 0 < 1 + r := by linarith
  calc
    ‖1 - z‖ ≤ (2 * ‖1 - (r : ℂ) * z‖) / (1 + r) := (le_div_iff₀ hp).mpr (by nlinarith)
    _ = _ := by ring

noncomputable def radialFlatProduct (N : ℕ) (w : ℕ → ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ range N, (1 - (r : ℂ) * z ^ (i + 1)) ^ w i

theorem radialFlatProduct_norm (N : ℕ) (w : ℕ → ℕ) (r : ℝ) (z : ℂ) :
    ‖radialFlatProduct N w r z‖ =
      ∏ i ∈ range N, ‖1 - (r : ℂ) * z ^ (i + 1)‖ ^ w i := by
  simp only [radialFlatProduct, norm_prod, norm_pow]

theorem flatPolynomial_norm_le_radial (N : ℕ) (w : ℕ → ℕ)
    (z : ℂ) (hz : ‖z‖ = 1) (r : ℝ) (hr : 0 ≤ r) :
    ‖((flatPolynomial N w).map (Int.castRingHom ℂ)).eval z‖ ≤
      (2 / (1 + r)) ^ weightMass N w * ‖radialFlatProduct N w r z‖ := by
  have hC : 0 ≤ 2 / (1 + r) := by positivity
  simp only [flatPolynomial, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X, eval_prod, eval_pow, eval_sub, eval_one, eval_X,
    norm_prod, norm_pow]
  calc
    _ ≤ ∏ i ∈ range N, ((2 / (1 + r)) * ‖1 - (r : ℂ) * z ^ (i + 1)‖) ^ w i := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact unit_circle_radial_ratio (z ^ (i + 1)) (by simp only [norm_pow, hz, one_pow]) r hr
    _ = _ := by
      simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, radialFlatProduct_norm, weightMass]

end Erdos345
