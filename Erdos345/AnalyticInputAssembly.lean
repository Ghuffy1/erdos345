import Erdos345.FiniteThresholdInversion

namespace Erdos345

/-- Full logical assembly from two explicit analytic inputs. Neither
input is asserted by this theorem, so this is not an unconditional solution. -/
theorem intended_of_cosine_and_shifted_prime_abundance
    (hcosine : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5)
    (hprimes : ∀ B : ℕ, ∃ t : ℕ, B ≤ t ∧ 2 ≤ t ∧
      32768 * logScale (2 * (t + 1)) ^ 8 ≤ ((shiftedPrimes t).card : ℝ)) :
    IntendedStatement := by
  obtain ⟨K, hK⟩ := good_degrees_threshold_upper hcosine
  apply intended_of_late_powerThreshold_inversions
  intro B
  obtain ⟨t, hBt, ht, hmany⟩ := hprimes (max B K)
  obtain ⟨k, htk, hk2, _, hupper⟩ := hK (t + 1) (by omega)
  have hlt := upper_envelope_lt_threshold_of_many_primes t k ht htk hk2 hmany
  exact ⟨t + 1, k, by omega, htk, hupper.trans_lt hlt⟩

end Erdos345
