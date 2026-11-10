import Erdos345.LogarithmicBudgetBounds

namespace Erdos345

theorem energyHeightConstant_le_logScale (k : ℕ) (hk : 0 < k) :
    energyHeightConstant (k + 1) ((k : ℝ) ^ 2 / 4) ≤ (3 + Real.log 64) * logScale k := by
  let K := logScale k
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlogk : Real.log (k : ℝ) ≤ K := by
    have h := Real.log_le_log hkR (show (k : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show k ≤ 2 * k by omega))
    dsimp only [K, logScale]
    linarith
  have hlogN : Real.log ((k + 1 : ℕ) : ℝ) ≤ K := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
      (show ((k + 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show k + 1 ≤ 2 * k by omega))
    dsimp only [K, logScale]
    linarith
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by have := Real.one_le_pi_div_two; linarith)
  have hfour : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hsixtyfour : 0 ≤ Real.log (64 : ℝ) := Real.log_nonneg (by norm_num)
  have hE : Real.log ((k : ℝ) ^ 2 / 4) = 2 * Real.log k - Real.log 4 := by
    rw [Real.log_div (ne_of_gt (sq_pos_of_pos hkR)) (by norm_num), Real.log_pow]
    norm_num
  have hden : Real.log (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) =
      Real.log Real.pi - Real.log 64 - Real.log ((k + 1 : ℕ) : ℝ) := by
    rw [Real.log_div (ne_of_gt Real.pi_pos) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    ring
  unfold energyHeightConstant
  change max 0 _ ≤ (3 + Real.log 64) * K
  apply max_le
  · positivity
  · rw [hE, hden]
    have hmul := mul_nonneg hsixtyfour (sub_nonneg.mpr hK)
    nlinarith

noncomputable def centerExponentConstant : ℝ :=
  4 * (3 * (1 / Real.log 2 + 5) ^ 2) *
    (2 * (4 / Real.log 2 + 12) + 2 * (3 + Real.log 64) + 16)

theorem centerExponentConstant_nonneg : 0 ≤ centerExponentConstant := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog64 : 0 ≤ Real.log (64 : ℝ) := Real.log_nonneg (by norm_num)
  unfold centerExponentConstant
  positivity

/-- The elementary good-degree variant needs only a fifth-power logarithmic
window exponent in its finite central-energy criterion. -/
theorem centerWindowExponent_le_logScale (Y k : ℕ) (hk : 0 < k) (hYk : Y ≤ k) :
    centerWindowExponent k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k) ≤
      centerExponentConstant * logScale k ^ 5 := by
  let K := logScale k
  let Cc := 3 * (1 / Real.log 2 + 5) ^ 2
  let Ch := 4 / Real.log 2 + 12
  let Cr := 3 + Real.log 64
  let Cd := 2 * Ch + 2 * Cr + 16
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hK0 : 0 ≤ K := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog64 : 0 ≤ Real.log (64 : ℝ) := Real.log_nonneg (by norm_num)
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hCh : 0 ≤ Ch := by dsimp only [Ch]; positivity
  have hCr : 0 ≤ Cr := by dsimp only [Cr]; positivity
  have hCd : 0 ≤ Cd := by dsimp only [Cd]; positivity
  have hc : conductorCoefficient (k + 1) k ≤ Cc * K ^ 2 := conductorCoefficient_le_logScale k hk
  have hh : goodConductorEnvelope Y k ≤ Ch * K ^ 3 := goodConductorEnvelope_le_logScale Y k hk hYk
  have hr : energyHeightConstant (k + 1) ((k : ℝ) ^ 2 / 4) ≤ Cr * K := energyHeightConstant_le_logScale k hk
  have hlogN : Real.log ((k + 1 : ℕ) : ℝ) ≤ K := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
      (show ((k + 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show k + 1 ≤ 2 * k by omega))
    dsimp only [K, logScale]
    linarith
  have hlogN0 : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 1 by omega))
  have hh0 := goodConductorEnvelope_nonneg Y k hk
  have hr0 : 0 ≤ energyHeightConstant (k + 1) ((k : ℝ) ^ 2 / 4) := le_max_left _ _
  have hKcube : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ (3 : ℕ))
  have hlinear : (2 * Cr + 16) * K ≤ (2 * Cr + 16) * K ^ 3 :=
    mul_le_mul_of_nonneg_left hKcube (by positivity)
  have hD : 2 * goodConductorEnvelope Y k +
      2 * energyHeightConstant (k + 1) ((k : ℝ) ^ 2 / 4) + 16 * Real.log ((k + 1 : ℕ) : ℝ) ≤
        Cd * K ^ 3 := by
    dsimp only [Cd]
    nlinarith
  unfold centerWindowExponent
  calc
    _ ≤ 4 * (Cc * K ^ 2) * (Cd * K ^ 3) := by gcongr
    _ = centerExponentConstant * logScale k ^ 5 := by
      dsimp only [Cc, Ch, Cr, Cd, K, centerExponentConstant]
      ring

end Erdos345
