import Erdos345.FlatInverseRadius

namespace Erdos345

open Finset

theorem sine_square_perturbation (x y : ℝ) :
    Real.sin (Real.pi * x) ^ 2 ≤ 2 * Real.sin (Real.pi * y) ^ 2 +
      2 * Real.pi ^ 2 * (x - y) ^ 2 := by
  have h := Real.abs_sin_sub_sin_le (Real.pi * x) (Real.pi * y)
  rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos] at h
  have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
  simp only [sq_abs, mul_pow] at hs
  nlinarith [sq_nonneg (Real.sin (Real.pi * x) - 2 * Real.sin (Real.pi * y))]

theorem sineEnergy_perturbation (f g : ℕ → ℝ) (X : ℕ) :
    sineEnergy f X ≤ 2 * sineEnergy g X +
      2 * Real.pi ^ 2 * ∑ n ∈ range X, (f n - g n) ^ 2 := by
  unfold sineEnergy
  calc
    _ ≤ ∑ n ∈ range X, (2 * Real.sin (Real.pi * g n) ^ 2 +
        2 * Real.pi ^ 2 * (f n - g n) ^ 2) :=
      sum_le_sum (fun n _ => sine_square_perturbation (f n) (g n))
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]

theorem power_phase_squared_distance_sum_le (α β : ℝ) (k X : ℕ) :
    (∑ n ∈ range X, (α * (n : ℝ) ^ k - β * (n : ℝ) ^ k) ^ 2) ≤
      (X : ℝ) * (α - β) ^ 2 * ((X : ℝ) ^ k) ^ 2 := by
  calc
    _ = ∑ n ∈ range X, (α - β) ^ 2 * ((n : ℝ) ^ k) ^ 2 := by
      apply sum_congr rfl
      intro n _
      ring
    _ ≤ ∑ _n ∈ range X, (α - β) ^ 2 * ((X : ℝ) ^ k) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hnX : (n : ℝ) ≤ X := by exact_mod_cast (mem_range.mp hn).le
      gcongr
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

theorem power_sineEnergy_perturbation (α β : ℝ) (k X : ℕ) :
    sineEnergy (fun n => α * (n : ℝ) ^ k) X ≤
      2 * sineEnergy (fun n => β * (n : ℝ) ^ k) X +
        2 * Real.pi ^ 2 * (X : ℝ) * (α - β) ^ 2 * ((X : ℝ) ^ k) ^ 2 := by
  have h := sineEnergy_perturbation (fun n => α * (n : ℝ) ^ k) (fun n => β * (n : ℝ) ^ k) X
  have he := mul_le_mul_of_nonneg_left (power_phase_squared_distance_sum_le α β k X)
    (show 0 ≤ 2 * Real.pi ^ 2 by positivity)
  nlinarith

theorem sineEnergy_mono (f : ℕ → ℝ) {X Y : ℕ} (hXY : X ≤ Y) :
    sineEnergy f X ≤ sineEnergy f Y := by
  apply sum_le_sum_of_subset_of_nonneg (range_mono hXY)
  intro n _ _
  exact sq_nonneg _

end Erdos345
