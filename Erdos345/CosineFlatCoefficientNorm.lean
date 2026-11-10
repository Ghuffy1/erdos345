import Erdos345.PolynomialCoefficientBound

namespace Erdos345

noncomputable def flatNormConstant : ℝ := (2 : ℝ) ^ 32 + 5

theorem flatNormConstant_nonneg : 0 ≤ flatNormConstant := by unfold flatNormConstant; positivity

/-- The norm transfer from the exact nonnegative-cosine input. The existence
of weights satisfying that input is not assumed or proved by this lemma. -/
theorem flat_coefficient_norm_from_cosine (J : ℕ) (hJ : 0 < J) (w : ℕ → ℕ) (a : ℝ)
    (hmass : weightMass J w = J) (hcos : flatCosineNonnegative J w a)
    (ha : a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    coefficientL1 (flatPolynomial J w) ≤
      Real.exp (flatNormConstant * (1 + Real.log (J : ℝ)) ^ 6) := by
  let L := Real.log (J : ℝ)
  let K := 1 + L
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J from hJ)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hL : 0 ≤ L := Real.log_nonneg hJ1
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have hK0 : 0 ≤ K := by linarith
  have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
  have hKle : K ≤ K ^ 6 := by simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ (6 : ℕ))
  have hcoef := coefficientL1_flat_from_cosine J w a hcos (by omega)
  rw [hmass] at hcoef
  have hsize : (J : ℝ) * J + 1 ≤ ((J : ℝ) + 1) ^ 2 := by nlinarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogJ1 : Real.log ((J : ℝ) + 1) ≤ 1 + L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (J : ℝ) + 1)
      (show (J : ℝ) + 1 ≤ 2 * J by linarith)
    rw [Real.log_mul (by norm_num) (ne_of_gt hJpos)] at h
    dsimp only [L]
    linarith
  have haL : a * L ≤ (2 : ℝ) ^ 32 * K ^ 6 := by
    have h1 := mul_le_mul_of_nonneg_right ha hL
    have h2 : K ^ 5 * L ≤ K ^ 6 := by
      have h := mul_le_mul_of_nonneg_left (show L ≤ K by dsimp only [K]; linarith) (pow_nonneg hK0 5)
      simpa only [← pow_succ] using h
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (2 : ℝ) ^ 32 by positivity)
    dsimp only [K, L] at h1 h3 ⊢
    nlinarith
  have hexponent : 2 * Real.log ((J : ℝ) + 1) + 1 + a * L ≤ flatNormConstant * K ^ 6 := by
    unfold flatNormConstant
    nlinarith
  calc
    coefficientL1 (flatPolynomial J w) ≤ ((J : ℝ) * J + 1) * Real.exp (1 + a * L) := hcoef
    _ ≤ ((J : ℝ) + 1) ^ 2 * Real.exp (1 + a * L) :=
      mul_le_mul_of_nonneg_right hsize (Real.exp_pos _).le
    _ = Real.exp (2 * Real.log ((J : ℝ) + 1) + 1 + a * L) := by
      have hp : ((J : ℝ) + 1) ^ 2 = Real.exp (2 * Real.log ((J : ℝ) + 1)) := by
        rw [show 2 * Real.log ((J : ℝ) + 1) = Real.log ((J : ℝ) + 1) + Real.log ((J : ℝ) + 1) by ring,
          Real.exp_add, Real.exp_log (by positivity : 0 < (J : ℝ) + 1), pow_two]
      rw [hp, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

theorem flat_coefficient_norm_below_degree (k J : ℕ) (hk : 0 < k) (hJ : 0 < J)
    (hJk : J ≤ k + 1) (w : ℕ → ℕ) (a : ℝ)
    (hmass : weightMass J w = J) (hcos : flatCosineNonnegative J w a)
    (ha : a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    coefficientL1 (flatPolynomial J w) ≤ Real.exp (flatNormConstant * logScale k ^ 6) := by
  have hlog : 1 + Real.log (J : ℝ) ≤ logScale k := by
    have h := Real.log_le_log (by exact_mod_cast hJ)
      (show (J : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show J ≤ 2 * k by omega))
    unfold logScale
    linarith
  have hnonneg : 0 ≤ 1 + Real.log (J : ℝ) := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ J by exact_mod_cast (show 1 ≤ J from hJ))
    linarith
  exact (flat_coefficient_norm_from_cosine J hJ w a hmass hcos ha).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hlog 6) flatNormConstant_nonneg))

end Erdos345
