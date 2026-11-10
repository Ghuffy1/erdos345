import Erdos345.FourierParameterGrowth

namespace Erdos345

open Filter

theorem eventually_inverse_factor_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (C * logScale k ^ 6) ^ 2 * fourierH k / 4 + 1 ≤
        Real.exp (logScale k ^ 8 / 4) := by
  filter_upwards [eventually_monomial_exp_dominated 1 8 (2 * C) 66051 (by norm_num),
    eventually_ge_atTop 1] with k hm hk
  simp only [pow_one] at hm
  let B := Real.exp (C * logScale k ^ 6)
  have hB : 1 ≤ B := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg hC (pow_nonneg (by linarith [logScale_ge_one k (by omega)]) 6)
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hBH : 0 ≤ B ^ 2 * fourierH k := mul_nonneg (sq_nonneg B) (fourierH_nonneg k)
  have hM : B ^ 2 * fourierH k / 4 + 1 ≤ B ^ 2 * (fourierH k + 1) := by nlinarith
  have heq : B ^ 2 = Real.exp ((2 * C) * logScale k ^ 6) := by
    dsimp only [B]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ B ^ 2 * (fourierH k + 1) := hM
    _ ≤ B ^ 2 * (66051 * (k : ℝ) * logScale k ^ 8) :=
      mul_le_mul_of_nonneg_left (fourierH_add_one_le k (by omega)) (sq_nonneg B)
    _ = 66051 * (k : ℝ) * logScale k ^ 8 * Real.exp ((2 * C) * logScale k ^ 6) := by rw [heq]; ring
    _ ≤ _ := hm

theorem eventually_fourier_degree_bound :
    ∀ᶠ k : ℕ in atTop, (((k + 1 : ℕ) : ℝ)) ^ 2 ≤ Real.exp (logScale k ^ 8 / 4) := by
  filter_upwards [eventually_monomial_exp_dominated 2 0 0 4 (by norm_num),
    eventually_ge_atTop 1] with k hm hk
  simp only [pow_zero, zero_mul, Real.exp_zero, mul_one] at hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h : (((k + 1 : ℕ) : ℝ)) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by
    have hle : ((k + 1 : ℕ) : ℝ) ≤ 2 * k := by push_cast; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ)) hle 2
    nlinarith only [hp]
  exact h.trans hm

theorem eventually_exp_quarter_ge_eight :
    ∀ᶠ k : ℕ in atTop, 8 ≤ Real.exp (logScale k ^ 8 / 4) := by
  have h := eventually_monomial_exp_dominated 0 0 0 8 (by norm_num)
  simpa only [pow_zero, zero_mul, Real.exp_zero, mul_one] using h

/-- One common eventual prefix bound works for every flat product
having the stated mass and coefficient norm. -/
theorem eventually_fourier_inverse_size (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop, ∀ w : ℕ → ℕ,
      weightMass (k + 1) w = k + 1 →
      coefficientL1 (flatPolynomial (k + 1) w) ≤ Real.exp (C * logScale k ^ 6) →
      ((fourierW k : ℝ) + 1) *
        (coefficientL1 (flatPolynomial (k + 1) w) ^ 2 * fourierH k / 4 + 1) +
        (flatPolynomial (k + 1) w).natDegree ≤ unreservedEndpoint (fourierN k) k + 1 := by
  filter_upwards [eventually_inverse_factor_bound C hC, eventually_fourier_degree_bound,
    eventually_exp_quarter_ge_eight, eventually_ge_atTop 4] with k hfactor hdegree hQ8 hk
  intro w hmass hnorm
  let A := logScale k ^ 8
  let Q := Real.exp (A / 4)
  let R := Real.exp (A / 2)
  let M := coefficientL1 (flatPolynomial (k + 1) w) ^ 2 * fourierH k / 4 + 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hQ0 : 0 ≤ Q := (Real.exp_pos _).le
  have hR1 : 1 ≤ R := Real.one_le_exp_iff.mpr (by positivity)
  have hH0 := fourierH_nonneg k
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hnorm2 := pow_le_pow_left₀ (coefficientL1_nonneg _) hnorm 2
  have hM : M ≤ Q := by
    have h := mul_le_mul_of_nonneg_right hnorm2 (fourierH_nonneg k)
    dsimp only [M, Q, A]
    linarith
  have hdNat : (flatPolynomial (k + 1) w).natDegree ≤ (k + 1) ^ 2 := by
    simpa only [hmass, pow_two] using flatPolynomial_natDegree_le (k + 1) w
  have hdCast : ((flatPolynomial (k + 1) w).natDegree : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) ^ 2 := by
    exact_mod_cast hdNat
  have hd : ((flatPolynomial (k + 1) w).natDegree : ℝ) ≤ Q := hdCast.trans hdegree
  have hW : (fourierW k : ℝ) + 1 ≤ 3 * R := (fourierW_bounds k).2
  have hstart : ((fourierW k : ℝ) + 1) * M +
      (flatPolynomial (k + 1) w).natDegree ≤ 3 * R * Q + Q := by gcongr
  have hsum : 3 * R * Q + Q ≤ 4 * R * Q := by nlinarith only [hR1, hQ0]
  have heq : R * Q * Q = Real.exp A := by
    dsimp only [R, Q]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hscale := mul_le_mul_of_nonneg_left hQ8 (show 0 ≤ R * Q by positivity)
  change R * Q * 8 ≤ R * Q * Q at hscale
  rw [heq] at hscale
  have hhalf : 4 * R * Q ≤ (fourierN k : ℝ) / 2 := by
    have hn := (fourierN_bounds k).1
    change Real.exp A ≤ (fourierN k : ℝ) at hn
    nlinarith only [hscale, hn]
  have hU := unreservedEndpoint_ge_three_quarters (fourierN k) k hk
  change ((fourierW k : ℝ) + 1) * M + (flatPolynomial (k + 1) w).natDegree ≤ _
  have hm := hstart.trans (hsum.trans hhalf)
  linarith

theorem eventually_fourier_center_prefix (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop,
      quasipolynomialCenterPrefix k C ≤ unreservedEndpoint (fourierN k) k + 1 := by
  filter_upwards [eventually_fourier_center_separation C hC, eventually_ge_atTop 4] with k hsep hk
  let X := quasipolynomialCenterPrefix k C
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast quasipolynomialCenterPrefix_pos k C
  have hXsq : (X : ℝ) ≤ (X : ℝ) ^ 2 := by nlinarith
  have hWN : (fourierW k : ℝ) ≤ fourierN k := by exact_mod_cast fourierW_le_N k
  have hU := unreservedEndpoint_ge_three_quarters (fourierN k) k hk
  have h : (X : ℝ) ≤ ((unreservedEndpoint (fourierN k) k + 1 : ℕ) : ℝ) := by
    push_cast
    change 8 * (X : ℝ) ^ 2 ≤ _ at hsep
    nlinarith
  exact_mod_cast h

end Erdos345
