import Erdos345.PrimeSubsetProducts

namespace Erdos345

/-- A convenient exact integer scale; its logarithm is linear in `Y`. -/
def primeProgressionScale (Y : ℕ) : ℕ := 4 ^ (Y + 1)

theorem prime_progression_scale_twice_primorial (Y : ℕ) :
    2 * primorial Y ≤ primeProgressionScale Y := by
  have hp := primorial_le_four_pow Y
  unfold primeProgressionScale
  rw [pow_succ]
  omega

theorem prime_progression_scale_ge (Y : ℕ) : Y ≤ primeProgressionScale Y := by
  have hp : Y ≤ primorial Y := le_primorial_self
  have hx := prime_progression_scale_twice_primorial Y
  omega

theorem log_prime_progression_scale (Y : ℕ) :
    Real.log (primeProgressionScale Y : ℝ) = ((Y : ℝ) + 1) * Real.log 4 := by
  simp only [primeProgressionScale, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add,
    Nat.cast_one]

theorem log_prime_progression_scale_bounds (Y : ℕ) (hY : 1 ≤ Y) :
    (Y : ℝ) ≤ Real.log (primeProgressionScale Y : ℝ) ∧
      Real.log (primeProgressionScale Y : ℝ) ≤ 4 * Y := by
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 := log_two_profile_bounds
  rw [log_prime_progression_scale, hl4]
  constructor <;> nlinarith

theorem prime_subset_products_twenty_four_lower (Y : ℕ) (hY : 16384 ≤ Y) :
    (Y : ℝ) ^ 12 / (2 ^ 24 * (Nat.factorial 24 : ℝ)) ≤
      (primeSubsetProducts Y 24).card := by
  have hpi := prime_count_sqrt_lower Y hY
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg Y)
  have hs0 := Real.sqrt_nonneg (Y : ℝ)
  have hYR : (16384 : ℝ) ≤ Y := by exact_mod_cast hY
  have hs : 128 ≤ Real.sqrt (Y : ℝ) := by nlinarith
  have hpc : 48 ≤ (Nat.primesLE Y).card := by
    have hh : (48 : ℝ) ≤ (Nat.primesLE Y).card := by linarith
    exact_mod_cast hh
  have hpow := pow_le_pow_left₀ hs0 hpi 24
  have hsq : Real.sqrt (Y : ℝ) ^ 24 = (Y : ℝ) ^ 12 := by
    calc
      Real.sqrt (Y : ℝ) ^ 24 = (Real.sqrt (Y : ℝ) ^ 2) ^ 12 := by rw [← pow_mul]
      _ = (Y : ℝ) ^ 12 := by rw [hs2]
  rw [hsq] at hpow
  rw [prime_subset_products_card]
  exact (div_le_div_of_nonneg_right hpow (by positivity)).trans
    (choose_lower_half (Nat.primesLE Y).card 24 (by omega))

end Erdos345
