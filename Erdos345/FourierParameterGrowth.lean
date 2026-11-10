import Erdos345.FourierParameters
import Erdos345.FinitePerturbationBudget

namespace Erdos345

open Filter

theorem eventually_fourier_energy_margin :
    ∀ᶠ k : ℕ in atTop, 2 * fourierH k + 8 ≤ (k : ℝ) ^ 2 := by
  filter_upwards [eventually_logScale_pow_small 8 262144 1 (by norm_num),
    eventually_ge_atTop 2048] with k hK hk
  have hkR : (2048 : ℝ) ≤ k := by exact_mod_cast hk
  have hprod := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg (α := ℝ) k)
  have hsq : (2048 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by gcongr
  unfold fourierH
  nlinarith

theorem eventually_fourier_root_budget :
    ∀ᶠ k : ℕ in atTop,
      Real.log ((fourierN k : ℝ) + 1) ≤ (k : ℝ) * Real.log (3 / 2) := by
  have hL : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards [eventually_logScale_pow_small 8 2 (Real.log (3 / 2)) hL,
    eventually_logScale_pow_small 0 4 (Real.log (3 / 2)) hL] with k hK hconst
  have hb := log_fourierN_add_one_le k
  simp only [pow_zero, mul_one] at hconst
  nlinarith

theorem exp_quarter_le_exp_half (k : ℕ) :
    Real.exp (logScale k ^ 8 / 4) ≤ Real.exp (logScale k ^ 8 / 2) := by
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ logScale k ^ 8 := by positivity
  linarith

theorem eventually_fourier_coarse_window :
    ∀ᶠ k : ℕ in atTop, 128000 * (k : ℝ) * (fourierH k + 1) ≤ fourierW k := by
  filter_upwards [eventually_monomial_exp_dominated 2 8 0 (128000 * 66051) (by norm_num),
    eventually_ge_atTop 1] with k hm hk
  simp only [zero_mul, Real.exp_zero, mul_one] at hm
  have hh := mul_le_mul_of_nonneg_left (fourierH_add_one_le k (by omega))
    (show 0 ≤ 128000 * (k : ℝ) by positivity)
  calc
    _ ≤ 128000 * (k : ℝ) * (66051 * (k : ℝ) * logScale k ^ 8) := hh
    _ = (128000 * 66051) * (k : ℝ) ^ 2 * logScale k ^ 8 := by ring
    _ ≤ Real.exp (logScale k ^ 8 / 4) := hm
    _ ≤ Real.exp (logScale k ^ 8 / 2) := exp_quarter_le_exp_half k
    _ ≤ _ := (fourierW_bounds k).1

theorem eventually_fourier_chebyshev_length :
    ∀ᶠ k : ℕ in atTop,
      256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * fourierW k := by
  filter_upwards [eventually_monomial_exp_dominated 4 0 0 4096 (by norm_num),
    eventually_ge_atTop 1] with k hm hk
  simp only [zero_mul, pow_zero, Real.exp_zero, mul_one] at hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (((k + 1 : ℕ) : ℝ)) ^ 4 ≤ (2 * (k : ℝ)) ^ 4 := by
    gcongr
    push_cast
    linarith
  have hp' : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ 4096 * (k : ℝ) ^ 4 := by nlinarith only [hp]
  have hW := (exp_quarter_le_exp_half k).trans (fourierW_bounds k).1
  have hpi : (fourierW k : ℝ) ≤ Real.pi * fourierW k := by
    have h := mul_le_mul_of_nonneg_right Real.two_le_pi (Nat.cast_nonneg (α := ℝ) (fourierW k))
    nlinarith [Nat.cast_nonneg (α := ℝ) (fourierW k)]
  exact hp'.trans (hm.trans (hW.trans hpi))

theorem eventually_fourier_center_separation (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k : ℕ in atTop,
      8 * (quasipolynomialCenterPrefix k C : ℝ) ^ 2 ≤ fourierW k := by
  let A := centerPrefixPowerConstant C + 1
  filter_upwards [eventually_monomial_exp_dominated 0 0 (2 * A) 8 (by norm_num),
    eventually_ge_atTop 1] with k hm hk
  simp only [pow_zero, mul_one] at hm
  have hXpos : (0 : ℝ) < quasipolynomialCenterPrefix k C := by
    exact_mod_cast quasipolynomialCenterPrefix_pos k C
  have hX : (quasipolynomialCenterPrefix k C : ℝ) ≤ Real.exp (A * logScale k ^ 6) :=
    (Real.log_le_iff_le_exp hXpos).mp (log_quasipolynomialCenterPrefix_le k (by omega) C hC)
  have hs := pow_le_pow_left₀ hXpos.le hX 2
  have heq : Real.exp (A * logScale k ^ 6) ^ 2 = Real.exp ((2 * A) * logScale k ^ 6) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hs
  exact (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8)).trans
    (hm.trans ((exp_quarter_le_exp_half k).trans (fourierW_bounds k).1))

end Erdos345
