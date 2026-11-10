import Erdos345.PrimeCountingUpper
import Erdos345.ReciprocalCountingProfile

namespace Erdos345

theorem belovMultiplicity_real_le (j : ℕ) :
    (belovMultiplicity j : ℝ) ≤ 1 + Real.log ((j + 1 : ℕ) : ℝ) := by
  have hn : 0 ≤ Real.log ((j + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j + 1 by omega))
  have h := Nat.floor_le hn
  unfold belovMultiplicity
  push_cast at h ⊢
  linarith

theorem belov_scale_log_lower (q j : ℕ) (hq : 256 ≤ q) :
    4 + 2 * Real.log ((j + 1 : ℕ) : ℝ) ≤ Real.log ((q * (j + 1) ^ 2 : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hj0 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hlq := Real.log_le_log (by norm_num : (0 : ℝ) < 256) (show (256 : ℝ) ≤ q by exact_mod_cast hq)
  have heq : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  rw [heq] at hlq
  push_cast at hj0 ⊢
  rw [Real.log_mul hq0.ne' (pow_pos hj0 2).ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith [log_two_profile_bounds.1]

theorem belovMultiplicity_twice_le_log_scale (q j : ℕ) (hq : 256 ≤ q) :
    2 * (belovMultiplicity j : ℝ) ≤ Real.log ((q * (j + 1) ^ 2 : ℕ) : ℝ) := by
  have hv := belovMultiplicity_real_le j
  have hl := belov_scale_log_lower q j hq
  linarith

theorem belovMultiplicity_square_le_log_scale (q j : ℕ) (hq : 256 ≤ q) :
    3 * (belovMultiplicity j : ℝ) ^ 2 ≤
      ((j + 1 : ℕ) : ℝ) * Real.log ((q * (j + 1) ^ 2 : ℕ) : ℝ) := by
  let l := Real.log ((j + 1 : ℕ) : ℝ)
  have hl : 0 ≤ l := Real.log_nonneg (by exact_mod_cast (show 1 ≤ j + 1 by omega))
  have hj : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have ht := Real.quadratic_le_exp_of_nonneg hl
  rw [Real.exp_log hj] at ht
  have hm := mul_le_mul_of_nonneg_right ht (show 0 ≤ 4 + 2 * l by linarith)
  have hcube : 0 ≤ l ^ 3 := pow_nonneg hl _
  have hsquare : 3 * (1 + l) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) * (4 + 2 * l) := by
    nlinarith
  have hv := pow_le_pow_left₀ (Nat.cast_nonneg (belovMultiplicity j)) (belovMultiplicity_real_le j) 2
  have hlog := mul_le_mul_of_nonneg_left (belov_scale_log_lower q j hq) hj.le
  dsimp only [l] at hsquare
  nlinarith

theorem sum_belov_primes_mul_log (q j : ℕ) (hq : 256 ≤ q) :
    (∑ p ∈ belovLevelPrimes q j, (p : ℝ)) * Real.log ((q * (j + 1) ^ 2 : ℕ) : ℝ) ≤
      5 * ((q * (j + 1) ^ 2 : ℕ) : ℝ) ^ 2 := by
  let X := q * (j + 1) ^ 2
  have hX : 2 ≤ X := by dsimp only [X]; nlinarith [Nat.one_le_pow 2 (j + 1) (by omega : 1 ≤ j + 1)]
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hcard : (belovLevelPrimes q j).card ≤ Nat.primeCounting X := by
    calc
      _ ≤ (Nat.primesLE X).card := Finset.card_le_card (Finset.erase_subset 2 (Nat.primesLE X))
      _ = _ := Nat.primesLE_card_eq_primeCounting X
  have hs : (∑ p ∈ belovLevelPrimes q j, (p : ℝ)) ≤ (X : ℝ) * Nat.primeCounting X := by
    calc
      _ ≤ ∑ _p ∈ belovLevelPrimes q j, (X : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact_mod_cast (Finset.mem_Icc.mp (belovLevelPrimes_subset q j hp)).2
      _ = (belovLevelPrimes q j).card * (X : ℝ) := by simp
      _ ≤ (Nat.primeCounting X : ℝ) * X := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hX0
      _ = _ := by ring
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hp := (le_div_iff₀ hlog).mp (primeCounting_le_five_mul_div_log X hX)
  have hmul := mul_le_mul_of_nonneg_left hp hX0
  exact (mul_le_mul_of_nonneg_right hs hlog.le).trans (by nlinarith)

theorem belov_level_count_bound (q j : ℕ) (hq : 256 ≤ q) :
    (belovMultiplicity j : ℝ) * (∑ p ∈ belovLevelPrimes q j, (p : ℝ)) ≤
      (5 / 2 : ℝ) * (q : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 4 := by
  have hs0 : 0 ≤ ∑ p ∈ belovLevelPrimes q j, (p : ℝ) := Finset.sum_nonneg (fun p _ => Nat.cast_nonneg p)
  have hv := mul_le_mul_of_nonneg_right (belovMultiplicity_twice_le_log_scale q j hq) hs0
  have hs := sum_belov_primes_mul_log q j hq
  push_cast at hs hv ⊢
  nlinarith

theorem belov_level_reciprocal_numerator_bound (q j : ℕ) (hq : 256 ≤ q) :
    (belovMultiplicity j : ℝ) ^ 2 * (∑ p ∈ belovLevelPrimes q j, (p : ℝ)) ≤
      (5 / 3 : ℝ) * (q : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 5 := by
  have hs0 : 0 ≤ ∑ p ∈ belovLevelPrimes q j, (p : ℝ) := Finset.sum_nonneg (fun p _ => Nat.cast_nonneg p)
  have hv := mul_le_mul_of_nonneg_right (belovMultiplicity_square_le_log_scale q j hq) hs0
  have hs := mul_le_mul_of_nonneg_left (sum_belov_primes_mul_log q j hq)
    (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))
  push_cast at hs hv ⊢
  nlinarith

end Erdos345
