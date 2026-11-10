import Erdos345.PrimePhaseDistance

namespace Erdos345

theorem abs_sine_round_shift (x : ℝ) :
    |Real.sin (Real.pi * (x - (round x : ℤ)))| = |Real.sin (Real.pi * x)| := by
  have heq : Real.pi * (x - (round x : ℤ)) =
      Real.pi * x - (round x : ℝ) * Real.pi := by ring
  rw [heq, Real.sin_sub_int_mul_pi, abs_mul]
  simp

theorem two_distance_le_abs_sine (x : ℝ) :
    2 * |x - (round x : ℤ)| ≤ |Real.sin (Real.pi * x)| := by
  have hd := abs_sub_round x
  have hp : |Real.pi * (x - (round x : ℤ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hp
  rw [abs_sine_round_shift] at hs
  calc
    2 * |x - (round x : ℤ)| =
        2 / Real.pi * |Real.pi * (x - (round x : ℤ))| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    _ ≤ _ := hs

theorem scaledSineBlock_abs_le_phaseDistance (p v : ℕ) (hp : 0 < p) (t : ℝ)
    (hd : 0 < primePhaseDistance (t / 2) p) :
    |scaledSineBlock p v t| ≤ (p : ℝ) / (2 * primePhaseDistance (t / 2) p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs := two_distance_le_abs_sine ((t / 2) / p)
  have heq : Real.pi * ((t / 2) / p) = Real.pi * t / (2 * (p : ℝ)) := by ring
  rw [heq] at hs
  have hdist := primePhaseDistance_eq (t / 2) p hp
  have hpos : 0 < |Real.sin (Real.pi * t / (2 * (p : ℝ)))| := by nlinarith
  have hbound := oddSineSum_abs_le_inv_sin (p * v) (Real.pi * t / (2 * (p : ℝ)))
    (abs_pos.mp hpos)
  change |scaledSineBlock p v t| ≤ _ at hbound
  have hden : 2 * primePhaseDistance (t / 2) p ≤
      (p : ℝ) * |Real.sin (Real.pi * t / (2 * (p : ℝ)))| := by nlinarith
  have hfrac : 1 / |Real.sin (Real.pi * t / (2 * (p : ℝ)))| ≤
      (p : ℝ) / (2 * primePhaseDistance (t / 2) p) := by
    apply (div_le_div_iff₀ hpos (by positivity)).mpr
    simpa using hden
  exact hbound.trans hfrac

theorem scaledSineBlock_abs_le_phaseBin (p v : ℕ) (hp : 0 < p) (t : ℝ)
    (hj : 0 < primePhaseBin (t / 2) p) :
    |scaledSineBlock p v t| ≤ (p : ℝ) / (2 * (primePhaseBin (t / 2) p : ℝ)) := by
  have hjR : (0 : ℝ) < primePhaseBin (t / 2) p := by exact_mod_cast hj
  have hjd := primePhaseBin_le_distance (t / 2) p
  have hd : 0 < primePhaseDistance (t / 2) p := hjR.trans_le hjd
  apply (scaledSineBlock_abs_le_phaseDistance p v hp t hd).trans
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg p) (by positivity)
  linarith

end Erdos345
