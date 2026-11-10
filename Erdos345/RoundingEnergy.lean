import Erdos345.CenterEnergy
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Field

namespace Erdos345

open Finset

theorem rounding_error_sine_bound (x : ℝ) :
    (x - (round x : ℝ)) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 / 4 := by
  let e := x - (round x : ℝ)
  have he : |e| ≤ 1 / 2 := abs_sub_round x
  have hangle : |Real.pi * e| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hangle
  have hscale : 2 / Real.pi * |Real.pi * e| = 2 * |e| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hscale] at hsin
  have hsquared := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * |e|) hsin 2
  have hperiod : Real.sin (Real.pi * e) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
    have harg : Real.pi * e = Real.pi * x - (round x : ℝ) * Real.pi := by
      dsimp only [e]
      ring
    rw [harg, Real.sin_sub_int_mul_pi, mul_pow]
    have hsign : ((-1 : ℝ) ^ round x) ^ 2 = 1 := by
      change (((-1 : ℝ) ^ round x) ^ (2 : ℤ)) = 1
      rw [← zpow_mul, Int.mul_comm (round x) 2, zpow_mul]
      norm_num
    rw [hsign, one_mul]
  rw [sq_abs, hperiod] at hsquared
  have he2 : |e| ^ 2 = e ^ 2 := sq_abs e
  dsimp only [e] at hsquared he2
  nlinarith

noncomputable def sineEnergy (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ range X, Real.sin (Real.pi * f n) ^ 2

theorem sineEnergy_nonneg (f : ℕ → ℝ) (X : ℕ) : 0 ≤ sineEnergy f X :=
  sum_nonneg (fun _ _ => sq_nonneg _)

theorem rounding_error_energy_le (f : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ range X, (f n - (round (f n) : ℝ)) ^ 2) ≤ sineEnergy f X / 4 := by
  calc
    (∑ n ∈ range X, (f n - (round (f n) : ℝ)) ^ 2) ≤
        ∑ n ∈ range X, Real.sin (Real.pi * f n) ^ 2 / 4 :=
      sum_le_sum (fun n _ => rounding_error_sine_bound (f n))
    _ = sineEnergy f X / 4 := by rw [← sum_div]; rfl

end Erdos345
