import Erdos345.PrimeProgressionUniform

namespace Erdos345

open Filter OAI.LargePrimeGaps
open scoped Topology

/-- Fixed powers of a logarithm are eventually bounded by every positive power. -/
theorem eventually_log_rpow_le_positive_rpow (a s : ℝ) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ a ≤ x ^ s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop a hs).bound (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)] with x h hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _), one_mul] using h

/-- Only fixed polylogarithmic moduli are needed for the shifted-prime application.
The premise is explicit: no prime-distribution theorem is postulated as an axiom. -/
theorem eventually_prime_progression_lower (hbv : BombieriVinogradov) :
    ∀ᶠ X : ℕ in atTop, ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ (Real.log (X : ℝ)) ^ 24 →
      (X : ℝ) / (2 * d.totient * Real.log (X : ℝ)) ≤ (primesOneMod X d).card := by
  obtain ⟨b, _hb, M, hM, x₀, _hx₀, hbound⟩ := hbv 30 (by norm_num)
  have hf : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hf
  filter_upwards [eventually_ge_atTop (2 : ℕ), hf.eventually_ge_atTop x₀,
    hl.eventually_ge_atTop (max 8 (4 * M)),
    hf.eventually (eventually_log_rpow_le_positive_rpow (24 + b) (1 / 2) (by norm_num)),
    hf.eventually (eventually_log_rpow_le_positive_rpow 26 (1 / 2) (by norm_num))]
    with X hX hx₀ hL hcut hpower
  have hL8 : 8 ≤ Real.log (X : ℝ) := (le_max_left _ _).trans hL
  have hMlog : 4 * M ≤ (Real.log (X : ℝ)) ^ 6 := by
    exact ((le_max_right _ _).trans hL).trans (le_self_pow₀ (by linarith) (by decide))
  have hp : (Real.log (X : ℝ)) ^ 26 ≤ Real.sqrt (X : ℝ) := by
    norm_num [Real.sqrt_eq_rpow] at hpower ⊢
    exact hpower
  exact prime_progression_uniform_of_bounds X b M hX hM hL8 hcut hMlog hp (hbound X hx₀)

end Erdos345
