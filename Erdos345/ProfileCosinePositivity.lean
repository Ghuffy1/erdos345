import Erdos345.FloorCosineProfile

namespace Erdos345

theorem belov_scaled_sine_identity (q m : ℕ) (θ : ℝ) (a : BelovFamilyIndex q) :
    Real.sin (((m : ℝ) / belovDenominator q a) * θ) =
      Real.sin (Real.pi * ((m : ℝ) * θ / Real.pi) / belovDenominator q a) := by
  congr 1
  field_simp [Real.pi_ne_zero]

theorem profile_cosine_nonneg_of_sine_nonneg (q m : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (hsine : 0 ≤ ∑' a : BelovFamilyIndex q,
      Real.sin (((m : ℝ) / belovDenominator q a) * θ)) :
    0 ≤ 2 * belovProfileMajorant q m + ∑ i ∈ Finset.range m,
      (belovCountingProfile q ((m : ℝ) / ((i + 1 : ℕ) : ℝ)) : ℝ) *
        Real.cos (((i + 1 : ℕ) : ℝ) * θ) := by
  by_cases hθpos : 0 < θ
  · have hsin : Summable (fun a : BelovFamilyIndex q =>
        Real.sin (((m : ℝ) / belovDenominator q a) * θ)) := by
      simpa only [belov_scaled_sine_identity] using
        summable_belovSineFamily q ((m : ℝ) * θ / Real.pi)
    have hcos := (summable_belovFloorCosine q m θ).mul_left (2 * Real.sin (θ / 2))
    have hmaj := (belovProfileMajorant_summable q m).mul_left θ
    have hbound := hsin.tsum_le_tsum (fun a =>
      sine_le_truncatedCosine ((m : ℝ) / belovDenominator q a) θ
        (div_nonneg (Nat.cast_nonneg m) (belovDenominator_pos q a).le) hθ) (hcos.add hmaj)
    have heq : (∑' a, (2 * Real.sin (θ / 2) * belovFloorCosine q m θ a +
        θ * min 1 ((m : ℝ) / belovDenominator q a))) =
        2 * Real.sin (θ / 2) * (∑' a, belovFloorCosine q m θ a) +
          θ * belovProfileMajorant q m := by
      rw [hcos.tsum_add hmaj, tsum_mul_left, tsum_mul_left]
      rfl
    change _ ≤ ∑' a, (2 * Real.sin (θ / 2) * belovFloorCosine q m θ a +
      θ * min 1 ((m : ℝ) / belovDenominator q a)) at hbound
    rw [heq, tsum_belovFloorCosine] at hbound
    have hscale := mul_le_mul_of_nonneg_right (theta_le_four_sin_half hθ hπ)
      (belovProfileMajorant_nonneg q m)
    have hspos : 0 < Real.sin (θ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    nlinarith
  · have hz : θ = 0 := by linarith
    subst θ
    simp only [mul_zero, Real.cos_zero, mul_one]
    exact add_nonneg (mul_nonneg (by norm_num) (belovProfileMajorant_nonneg q m))
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

end Erdos345
