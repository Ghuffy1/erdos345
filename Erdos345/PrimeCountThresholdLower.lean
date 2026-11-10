import Erdos345.FiniteLowerBound
import Erdos345.ShiftedPrimeBound
import Erdos345.RadixCompleteness
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos345

theorem prime_product_ge_two_pow_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    2 ^ P.card ≤ ∏ p ∈ P, p := by
  calc
    2 ^ P.card = ∏ _p ∈ P, (2 : ℕ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun p hp => (hP p hp).two_le)

theorem sqrt_prime_product_ge_two_pow_half (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    2 ^ (P.card / 2) ≤ Nat.sqrt (∏ p ∈ P, p) := by
  apply Nat.le_sqrt.mpr
  rw [← pow_two]
  calc
    (2 ^ (P.card / 2)) ^ 2 = 2 ^ (2 * (P.card / 2)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ P.card := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ _ := prime_product_ge_two_pow_card P hP

theorem power_lt_sqrt_power_sub (Q t : ℕ) (hQ : 9 ≤ Q) (ht : 2 ≤ t) :
    (Nat.sqrt Q + 1) ^ t < (Nat.sqrt Q + 1) ^ (t + 1) - Q := by
  let x := Nat.sqrt Q + 1
  have hx : 2 ≤ x := by
    have hs : 3 ≤ Nat.sqrt Q := Nat.le_sqrt.mpr (by simpa using hQ)
    dsimp only [x]
    omega
  have hQx : Q < x ^ 2 := Nat.lt_succ_sqrt' Q
  have hp : x ^ 2 ≤ x ^ t := Nat.pow_le_pow_right (by omega) ht
  have hm : 2 * x ^ t ≤ x ^ (t + 1) := by
    rw [pow_succ]
    nlinarith
  change x ^ t < x ^ (t + 1) - Q
  omega

theorem two_pow_prime_count_lt_threshold (P : Finset ℕ) (t : ℕ) (ht : 2 ≤ t)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p - 1 ∣ t) (hcard : 4 ≤ P.card) :
    2 ^ ((P.card / 2) * t) < leastPowerThreshold (t + 1) := by
  have hQ : 9 ≤ ∏ p ∈ P, p := by
    have hprod := prime_product_ge_two_pow_card P hP
    have hp : 2 ^ 4 ≤ 2 ^ P.card := Nat.pow_le_pow_right (by decide) hcard
    norm_num at hp
    omega
  have hlower := threshold_lower_bound_from_shifted_primes P t (leastPowerThreshold (t + 1))
    (by omega) hP hdiv hQ (leastPowerThreshold_spec (t + 1) (by omega)).1
  have hpow := power_lt_sqrt_power_sub (∏ p ∈ P, p) t hQ ht
  have hroot := sqrt_prime_product_ge_two_pow_half P hP
  have hcompare : 2 ^ ((P.card / 2) * t) ≤ (Nat.sqrt (∏ p ∈ P, p) + 1) ^ t := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by omega) t
  exact hcompare.trans_lt (hpow.trans hlower)

theorem log_threshold_lower_of_prime_count (P : Finset ℕ) (t : ℕ) (ht : 2 ≤ t)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p - 1 ∣ t) (hcard : 4 ≤ P.card) :
    ((P.card / 2 : ℕ) : ℝ) * (t : ℝ) * Real.log 2 <
      Real.log (leastPowerThreshold (t + 1) : ℝ) := by
  have h := two_pow_prime_count_lt_threshold P t ht hP hdiv hcard
  have hr : (2 : ℝ) ^ ((P.card / 2) * t) < (leastPowerThreshold (t + 1) : ℝ) := by exact_mod_cast h
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ ((P.card / 2) * t)) hr
  simpa only [Real.log_pow, Nat.cast_mul] using hl

theorem shifted_prime_log_threshold_lower (t : ℕ) (ht : 2 ≤ t)
    (hcard : 4 ≤ (shiftedPrimes t).card) :
    (((shiftedPrimes t).card / 2 : ℕ) : ℝ) * (t : ℝ) * Real.log 2 <
      Real.log (leastPowerThreshold (t + 1) : ℝ) :=
  log_threshold_lower_of_prime_count (shiftedPrimes t) t ht
    (fun _p hp => (Finset.mem_filter.mp hp).2.1)
    (fun _p hp => (Finset.mem_filter.mp hp).2.2) hcard

end Erdos345
