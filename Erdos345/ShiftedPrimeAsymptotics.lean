import Erdos345.FiniteThresholdInversion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos345

open Filter
open scoped Topology

/-- Every fixed power is eventually smaller than exp(c*x/log x). -/
theorem eventually_power_lt_exp_div_log (c D : ℝ) (n : ℕ) (hc : 0 < c) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, D * x ^ n < Real.exp (c * x / Real.log x) := by
  let C := max (Real.log D) 0 + (n : ℝ) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)).const_mul C
  simp only [one_mul, add_zero, mul_zero] at ht
  have he := ht.eventually (gt_mem_nhds hc)
  filter_upwards [he, eventually_gt_atTop (Real.exp 1)] with x hx hxl
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  have hx0 : 0 < x := hexp.trans hxl
  have hlog1 : 1 < Real.log x := by
    have hh := Real.log_lt_log hexp hxl
    simpa only [Real.log_exp] using hh
  have hlog0 : 0 < Real.log x := by linarith
  have hbound : C * Real.log x ^ 2 < c * x := by
    have hh : C * Real.log x ^ 2 / x < c := by
      convert hx using 1
      ring
    exact (div_lt_iff₀ hx0).mp hh
  have hDlog : Real.log D ≤ max (Real.log D) 0 := le_max_left _ _
  have hmax0 : 0 ≤ max (Real.log D) 0 := le_max_right _ _
  have hscaled : (Real.log D + (n : ℝ) * Real.log x) * Real.log x < c * x := by
    have hmul := mul_le_mul_of_nonneg_right hDlog hlog0.le
    have hstep := mul_nonneg hmax0 (show 0 ≤ Real.log x ^ 2 - Real.log x by nlinarith)
    dsimp only [C] at hbound
    nlinarith
  apply (Real.log_lt_iff_lt_exp (mul_pos hD (pow_pos hx0 n))).mp
  rw [Real.log_mul hD.ne' (pow_ne_zero n hx0.ne'), Real.log_pow]
  exact (lt_div_iff₀ hlog0).mpr hscaled

theorem doubled_logScale_le (t : ℕ) (ht : 8 ≤ t) :
    logScale (2 * (t + 1)) ≤ 4 * Real.log (t : ℝ) := by
  have htR : (8 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogt := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ t by linarith)
  have hlog1 : 1 ≤ Real.log (t : ℝ) := by linarith
  have hpoly : (4 : ℝ) * ((t : ℝ) + 1) ≤ (t : ℝ) ^ 2 := by
    nlinarith [mul_nonneg ht0.le (show 0 ≤ (t : ℝ) - 8 by linarith)]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 4 * ((t : ℝ) + 1)) hpoly
  rw [Real.log_pow] at hlog
  unfold logScale
  push_cast
  rw [show (2 : ℝ) * (2 * ((t : ℝ) + 1)) = 4 * ((t : ℝ) + 1) by ring]
  norm_num at hlog
  linarith

theorem eventually_shifted_prime_requirement (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℕ in atTop,
      32768 * logScale (2 * (t + 1)) ^ 8 <
        Real.exp (c * Real.log (t : ℝ) / Real.log (Real.log (t : ℝ))) := by
  have htlog : Tendsto (fun t : ℕ => Real.log (t : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := htlog.eventually (eventually_power_lt_exp_div_log c (32768 * 4 ^ 8) 8 hc (by positivity))
  filter_upwards [he, eventually_ge_atTop 8] with t hbound ht
  have hs := doubled_logScale_le t ht
  have hs0 : 0 ≤ logScale (2 * (t + 1)) := by
    have hh := logScale_ge_one (2 * (t + 1)) (by omega)
    linarith
  have hp := pow_le_pow_left₀ hs0 hs 8
  calc
    32768 * logScale (2 * (t + 1)) ^ 8 ≤ 32768 * (4 * Real.log (t : ℝ)) ^ 8 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = (32768 * 4 ^ 8) * Real.log (t : ℝ) ^ 8 := by ring
    _ < _ := hbound

theorem shifted_prime_abundance_of_fan_input (c : ℝ) (hc : 0 < c)
    (hfan : ∀ B : ℕ, ∃ t : ℕ, B ≤ t ∧
      Real.exp (c * Real.log (t : ℝ) / Real.log (Real.log (t : ℝ))) < ((shiftedPrimes t).card : ℝ)) :
    ∀ B : ℕ, ∃ t : ℕ, B ≤ t ∧ 2 ≤ t ∧
      32768 * logScale (2 * (t + 1)) ^ 8 ≤ ((shiftedPrimes t).card : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_shifted_prime_requirement c hc)
  intro B
  obtain ⟨t, ht, hcard⟩ := hfan (max B (max 8 N))
  exact ⟨t, by omega, by omega, ((hN t (by omega)).trans hcard).le⟩

end Erdos345
