import Erdos345.ReciprocalCountingProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos345

noncomputable def initialCosineSum (n : ℕ) (θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, Real.cos (θ * (i : ℝ) + θ)

theorem initialCosineSum_identity (n : ℕ) (θ : ℝ) :
    2 * Real.sin (θ / 2) * initialCosineSum n θ =
      Real.sin (((n : ℝ) + 1 / 2) * θ) - Real.sin (θ / 2) := by
  have h := Real.sin_mul_sum_cos n θ θ
  change Real.sin (θ / 2) * initialCosineSum n θ = _ at h
  rw [Real.sin_sub_sin]
  have h₁ : (((n : ℝ) + 1 / 2) * θ - θ / 2) / 2 = (n : ℝ) * θ / 2 := by ring
  have h₂ : (((n : ℝ) + 1 / 2) * θ + θ / 2) / 2 = ((n : ℝ) - 1) * θ / 2 + θ := by ring
  rw [h₁, h₂]
  nlinarith [h]

theorem sine_le_truncatedCosine (t θ : ℝ) (ht : 0 ≤ t) (hθ : 0 ≤ θ) :
    Real.sin (t * θ) ≤
      2 * Real.sin (θ / 2) * initialCosineSum ⌊t⌋₊ θ + θ * min 1 t := by
  by_cases ht1 : t < 1
  · rw [Nat.floor_eq_zero.mpr ht1, initialCosineSum]
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, min_eq_right ht1.le]
    simpa only [mul_comm] using Real.sin_le (mul_nonneg ht hθ)
  · have hfloor := Nat.floor_le ht
    have hnext := Nat.lt_floor_add_one t
    have hround : |t * θ - ((⌊t⌋₊ : ℝ) + 1 / 2) * θ| ≤ θ / 2 := by
      apply abs_le.mpr
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hfloor) hθ]
      · nlinarith [mul_nonneg (show 0 ≤ (⌊t⌋₊ : ℝ) + 1 - t by linarith) hθ]
    have hlip := (Real.abs_sin_sub_sin_le (t * θ) (((⌊t⌋₊ : ℝ) + 1 / 2) * θ)).trans hround
    have hone := (le_abs_self (Real.sin (t * θ) -
      Real.sin (((⌊t⌋₊ : ℝ) + 1 / 2) * θ))).trans hlip
    have hsmall := Real.sin_le (show 0 ≤ θ / 2 by linarith)
    have hid := initialCosineSum_identity ⌊t⌋₊ θ
    rw [min_eq_left (le_of_not_gt ht1)]
    nlinarith

theorem theta_le_four_sin_half {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    θ ≤ 4 * Real.sin (θ / 2) := by
  have hj := Real.mul_le_sin (show 0 ≤ θ / 2 by linarith) (show θ / 2 ≤ Real.pi / 2 by linarith)
  have heq : 2 / Real.pi * (θ / 2) = θ / Real.pi := by ring
  rw [heq] at hj
  have ht : θ ≤ Real.pi * Real.sin (θ / 2) := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hj
    nlinarith
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  nlinarith [Real.pi_lt_four, mul_nonneg (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four]) hs]

end Erdos345
