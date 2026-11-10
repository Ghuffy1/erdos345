import Erdos345.WindowGrowth

namespace Erdos345

theorem sufficientCenterPrefix_pos (k W : ℕ) (B E : ℝ) (hE : 0 ≤ E) :
    0 < sufficientCenterPrefix k W B E := by
  have hpos : 0 < ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have h : (0 : ℝ) < (sufficientCenterPrefix k W B E : ℝ) := hpos.trans_le (Nat.le_ceil _)
  exact_mod_cast h

theorem log_sufficientCenterPrefix_le (k W : ℕ) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) :
    Real.log (sufficientCenterPrefix k W B E : ℝ) ≤
      Real.log 3 + Real.log ((W : ℝ) + 1) + 2 * Real.log (B + 1) +
        Real.log (E + 1) + 2 * Real.log ((k + 1 : ℕ) : ℝ) := by
  let D := (B + 1) ^ 2 * (E + 1)
  let N := ((k + 1 : ℕ) : ℝ) ^ 2
  let U := ((W : ℝ) + 1) * D * N
  have hD : 1 ≤ D := by
    dsimp only [D]
    have hb : (1 : ℝ) ≤ (B + 1) ^ 2 := by nlinarith
    have he : (1 : ℝ) ≤ E + 1 := by linarith
    nlinarith
  have hN : 1 ≤ N := by
    dsimp only [N]
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    nlinarith
  have hbase : B ^ 2 * E / 4 + 1 ≤ D := by
    have hprod : 0 ≤ B ^ 2 * E := mul_nonneg (sq_nonneg B) hE
    have hcompare : (B ^ 2 + 1) * (E + 1) ≤ D := by
      dsimp only [D]
      exact mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    nlinarith [sq_nonneg B]
  have hWD : 1 ≤ ((W : ℝ) + 1) * D := by
    have hw0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    have hw : (1 : ℝ) ≤ (W : ℝ) + 1 := by linarith
    nlinarith
  have hU1 : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) ≤ U := by
    have h := mul_le_mul_of_nonneg_left hbase (show 0 ≤ (W : ℝ) + 1 by positivity)
    dsimp only [U]
    nlinarith
  have hUN : N ≤ U := by dsimp only [U]; nlinarith
  have hU : 1 ≤ U := hN.trans hUN
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + N by dsimp only [N]; positivity)
  change (sufficientCenterPrefix k W B E : ℝ) < ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + N + 1 at hceil
  have hXU : (sufficientCenterPrefix k W B E : ℝ) ≤ 3 * U := by linarith
  have hXpos : (0 : ℝ) < sufficientCenterPrefix k W B E := by exact_mod_cast sufficientCenterPrefix_pos k W B E hE
  have hlog := Real.log_le_log hXpos hXU
  have hlogD : Real.log D = 2 * Real.log (B + 1) + Real.log (E + 1) := by
    dsimp only [D]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hlogU : Real.log U = Real.log ((W : ℝ) + 1) + Real.log D + 2 * Real.log ((k + 1 : ℕ) : ℝ) := by
    dsimp only [U, N]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by linarith), Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) (by linarith), hlogU, hlogD] at hlog
  linarith

noncomputable def centerPrefixLogConstant : ℝ := centerWindowLogConstant + 9

theorem centerPrefixLogConstant_nonneg : 0 ≤ centerPrefixLogConstant := by
  unfold centerPrefixLogConstant
  have := centerWindowLogConstant_nonneg
  linarith

theorem log_sufficientCenterPrefix_square_le (Y k : ℕ) (hk : 0 < k) (hYk : Y ≤ k)
    (B : ℝ) (hB : 0 ≤ B) :
    Real.log (sufficientCenterPrefix k
      (sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k)) B ((k : ℝ) ^ 2) : ℝ) ≤
      2 * Real.log (B + 1) + centerPrefixLogConstant * logScale k ^ 5 := by
  let W := sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k)
  let K := logScale k
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hK5 : 1 ≤ K ^ 5 := one_le_pow₀ hK
  have hKle : K ≤ K ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ (5 : ℕ))
  have hW : (1 : ℝ) ≤ W := by have h := sufficientCenterWindow_ge_sixteen k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k); change (16 : ℝ) ≤ W at h; linarith
  have hWplus : Real.log ((W : ℝ) + 1) ≤ Real.log 2 + Real.log (W : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (W : ℝ) + 1) (show (W : ℝ) + 1 ≤ 2 * W by linarith)
    rwa [Real.log_mul (by norm_num) (by linarith)] at h
  have hEplus : Real.log ((k : ℝ) ^ 2 + 1) ≤ 2 * Real.log ((k + 1 : ℕ) : ℝ) := by
    have hsq : (k : ℝ) ^ 2 + 1 ≤ (((k + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have h := Real.log_le_log (by positivity : 0 < (k : ℝ) ^ 2 + 1) hsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hN := log_succ_le_logScale k hk
  have hlogW := log_sufficientCenterWindow_le Y k hk hYk
  have h3 : Real.log (3 : ℝ) ≤ 3 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have h2 : Real.log (2 : ℝ) ≤ 2 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have h := log_sufficientCenterPrefix_le k W B ((k : ℝ) ^ 2) hB (sq_nonneg _)
  change Real.log (sufficientCenterPrefix k W B ((k : ℝ) ^ 2) : ℝ) ≤
    2 * Real.log (B + 1) + centerPrefixLogConstant * K ^ 5
  dsimp only [centerPrefixLogConstant]
  change Real.log (W : ℝ) ≤ centerWindowLogConstant * K ^ 5 at hlogW
  change Real.log ((k + 1 : ℕ) : ℝ) ≤ K at hN
  nlinarith

end Erdos345
