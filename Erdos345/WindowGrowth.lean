import Erdos345.EnergyScaleBound

namespace Erdos345

noncomputable def centerWindowLogConstant : ℝ := centerExponentConstant + 2048

theorem centerWindowLogConstant_nonneg : 0 ≤ centerWindowLogConstant := by
  unfold centerWindowLogConstant
  have := centerExponentConstant_nonneg
  linarith

theorem log_succ_le_logScale (k : ℕ) (hk : 0 < k) :
    Real.log ((k + 1 : ℕ) : ℝ) ≤ logScale k := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
    (show ((k + 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) by exact_mod_cast (show k + 1 ≤ 2 * k by omega))
  unfold logScale
  linarith

/-- A genuine logarithmic bound on the natural ceiling used for the
central recurrence window. This includes the polynomial size condition. -/
theorem log_sufficientCenterWindow_le (Y k : ℕ) (hk : 0 < k) (hYk : Y ≤ k) :
    Real.log (sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k) : ℝ) ≤
      centerWindowLogConstant * logScale k ^ 5 := by
  let K := logScale k
  let A := centerExponentConstant + 12
  let Z := A * K ^ 5
  let R := 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi
  let V := centerWindowExponent k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k)
  let W := sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k)
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hK0 : 0 ≤ K := by linarith
  have hK5 : 1 ≤ K ^ 5 := one_le_pow₀ hK
  have hKle : K ≤ K ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ (5 : ℕ))
  have hC : 0 ≤ centerExponentConstant := centerExponentConstant_nonneg
  have hA : 0 ≤ A := by dsimp only [A]; linarith
  have hZ : 0 ≤ Z := mul_nonneg hA (pow_nonneg hK0 _)
  have hV : V ≤ Z := by
    have h := centerWindowExponent_le_logScale Y k hk hYk
    dsimp only [V, Z, A]
    change _ ≤ (centerExponentConstant + 12) * K ^ 5
    nlinarith
  have h12 : 12 * K ≤ Z := by dsimp only [Z, A]; nlinarith
  have hN12 : ((k + 1 : ℕ) : ℝ) ^ 12 ≤ Real.exp (12 * K) := by
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (log_succ_le_logScale k hk) (by norm_num)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hR : R ≤ 1024 * Real.exp Z := by
    have hpi : 1 ≤ Real.pi := by have := Real.one_le_pi_div_two; linarith
    calc
      R ≤ 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 :=
        div_le_self (by positivity) hpi
      _ = 1024 * ((k + 1 : ℕ) : ℝ) ^ 12 := by ring
      _ ≤ 1024 * Real.exp (12 * K) := mul_le_mul_of_nonneg_left hN12 (by norm_num)
      _ ≤ 1024 * Real.exp Z := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h12) (by norm_num)
  have hexp1 : 1 ≤ Real.exp Z := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hZ
  have hceil : (W : ℝ) < 17 + R + Real.exp V := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 16 + R + Real.exp V by positivity)
    change (W : ℝ) < 16 + R + Real.exp V + 1 at h
    linarith
  have hWle : (W : ℝ) ≤ 1042 * Real.exp Z := by
    have hev := Real.exp_le_exp.mpr hV
    nlinarith
  have hWpos : (0 : ℝ) < W := by
    have h := sufficientCenterWindow_ge_sixteen k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k)
    change (16 : ℝ) ≤ W at h
    linarith
  have hlog := Real.log_le_log hWpos hWle
  rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos Z)), Real.log_exp] at hlog
  have hnum : Real.log (1042 : ℝ) ≤ 1042 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1042)
    linarith
  change Real.log (W : ℝ) ≤ centerWindowLogConstant * K ^ 5
  dsimp only [centerWindowLogConstant, Z, A] at *
  nlinarith

end Erdos345
