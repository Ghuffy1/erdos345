import Erdos345.BelovLargePositivity
import Erdos345.BelovProfileBudget

namespace Erdos345

/-- The previously unproved cosine-polynomial input is now supplied by
the explicit reciprocal family, global sine estimate and profile budget. -/
theorem belov_konyagin_input_proved : BelovKonyaginInput :=
  belov_input_of_global_sine_512 belovSineTotal_nonneg_512

/-- The entire good-degree threshold upper bound now has no analytic premise. -/
theorem good_degrees_threshold_upper_unconditional :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ,
      Y ≤ k ∧ k ≤ 2 * Y ∧ 20 ≤ k ∧
      leastPowerThreshold k ≤ 256 * (fourierN k) ^ (k + 1) :=
  good_degrees_threshold_upper belov_konyagin_input_proved

/-- The exact original target, with only the lower shifted-prime input remaining. -/
theorem intended_of_fan_pollack (hfan : FanPollackInput) : IntendedStatement :=
  intended_of_published_analytic_inputs belov_konyagin_input_proved hfan

/-- A weaker lower-input target that also suffices, without demanding
the full numerical constant in Fan--Pollack. This hypothesis remains unproved. -/
theorem intended_of_many_shifted_primes
    (hprimes : ∀ B : ℕ, ∃ t : ℕ, B ≤ t ∧ 2 ≤ t ∧
      32768 * logScale (2 * (t + 1)) ^ 8 ≤ ((shiftedPrimes t).card : ℝ)) :
    IntendedStatement :=
  intended_of_cosine_and_shifted_prime_abundance belov_konyagin_input_proved hprimes

end Erdos345
