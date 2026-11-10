import Erdos345.PrimeCountThresholdLower
import Erdos345.ThresholdUpperLog

namespace Erdos345

theorem many_shifted_primes_half_lower (t : ℕ)
    (hmany : 32768 * logScale (2 * (t + 1)) ^ 8 ≤ ((shiftedPrimes t).card : ℝ)) :
    4 ≤ (shiftedPrimes t).card ∧
      8192 * logScale (2 * (t + 1)) ^ 8 ≤ (((shiftedPrimes t).card / 2 : ℕ) : ℝ) := by
  have hK : 1 ≤ logScale (2 * (t + 1)) ^ 8 :=
    one_le_pow₀ (logScale_ge_one _ (by omega))
  have hr : ((shiftedPrimes t).card : ℝ) ≤
      2 * (((shiftedPrimes t).card / 2 : ℕ) : ℝ) + 1 := by
    have hm := Nat.mod_lt (shiftedPrimes t).card (show 0 < 2 by omega)
    have he := Nat.mod_add_div (shiftedPrimes t).card 2
    exact_mod_cast (show (shiftedPrimes t).card ≤ 2 * ((shiftedPrimes t).card / 2) + 1 by omega)
  constructor
  · have hc : (4 : ℝ) ≤ (shiftedPrimes t).card := by nlinarith
    exact_mod_cast hc
  · nlinarith

/-- An explicit finite sufficient condition for the bad-degree lower
bound to exceed every good-degree upper envelope in the next dyadic block. -/
theorem upper_envelope_lt_threshold_of_many_primes (t k : ℕ) (ht : 2 ≤ t)
    (hk : t + 1 ≤ k) (hk2 : k ≤ 2 * (t + 1))
    (hmany : 32768 * logScale (2 * (t + 1)) ^ 8 ≤ ((shiftedPrimes t).card : ℝ)) :
    256 * (fourierN k) ^ (k + 1) < leastPowerThreshold (t + 1) := by
  obtain ⟨hc, hr⟩ := many_shifted_primes_half_lower t hmany
  have hlogLower := shifted_prime_log_threshold_lower t ht hc
  have hlogUpper := log_threshold_envelope_le_at_larger (by omega : 0 < k) hk2
  let Q := logScale (2 * (t + 1)) ^ 8
  let r := (((shiftedPrimes t).card / 2 : ℕ) : ℝ)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hprod := mul_le_mul_of_nonneg_right hr ht0
  have hlogprod := mul_le_mul_of_nonneg_left hl2 (mul_nonneg hr0 ht0)
  have htQ := mul_le_mul_of_nonneg_right htR hQ
  have hcompare : 512 * ((2 * (t + 1) : ℕ) : ℝ) * Q ≤ r * (t : ℝ) * Real.log 2 := by
    change 8192 * Q * (t : ℝ) ≤ r * (t : ℝ) at hprod
    push_cast
    nlinarith only [hprod, hlogprod, htQ, hQ]
  have hlog : Real.log ((256 * (fourierN k) ^ (k + 1) : ℕ) : ℝ) <
      Real.log (leastPowerThreshold (t + 1) : ℝ) :=
    hlogUpper.trans_lt (hcompare.trans_lt hlogLower)
  have hupper0 : (0 : ℝ) < ((256 * (fourierN k) ^ (k + 1) : ℕ) : ℝ) := by
    have hp := fourierN_pos k
    positivity
  have hlower0 : (0 : ℝ) < (leastPowerThreshold (t + 1) : ℝ) := by
    have h := two_pow_prime_count_lt_threshold (shiftedPrimes t) t ht
      (fun _p hp => (Finset.mem_filter.mp hp).2.1)
      (fun _p hp => (Finset.mem_filter.mp hp).2.2) hc
    have hp : 0 < leastPowerThreshold (t + 1) := (by positivity : 0 < 2 ^ (((shiftedPrimes t).card / 2) * t)).trans h
    exact_mod_cast hp
  exact_mod_cast (Real.log_lt_log_iff hupper0 hlower0).mp hlog

end Erdos345
