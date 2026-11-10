import Erdos345.NaturalWindowCount
import Erdos345.DeletedPrefixEnergy

namespace Erdos345

set_option maxHeartbeats 20000

theorem sin_square_sub_integer (x : ℝ) (z : ℤ) :
    Real.sin (Real.pi * (x - z)) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
  have harg : Real.pi * (x - z) = Real.pi * x - (z : ℝ) * Real.pi := by ring
  rw [harg, Real.sin_sub_int_mul_pi, mul_pow]
  have hs : ((-1 : ℝ) ^ z) ^ 2 = 1 := by
    change (((-1 : ℝ) ^ z) ^ (2 : ℤ)) = 1
    rw [← zpow_mul, Int.mul_comm z 2, zpow_mul]
    norm_num
  rw [hs, one_mul]

theorem sine_square_lower_on_phase_window (x : ℝ) (z : ℤ)
    (hl : (z : ℝ) + 1 / 8 ≤ x) (hu : x ≤ (z : ℝ) + 1 / 4) :
    (1 : ℝ) / 16 ≤ Real.sin (Real.pi * x) ^ 2 := by
  let y := x - z
  have hy0 : 0 ≤ y := by dsimp only [y]; linarith
  have hy : y ≤ 1 / 4 := by dsimp only [y]; linarith
  have hyL : 1 / 8 ≤ y := by dsimp only [y]; linarith
  have hangle : |Real.pi * y| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hy0)]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hangle
  have hscale : 2 / Real.pi * |Real.pi * y| = 2 * y := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hy0)]
    field_simp
  rw [hscale] at hs
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * y) hs 2
  rw [sq_abs] at hsq
  have hp := sin_square_sub_integer x z
  change Real.sin (Real.pi * y) ^ 2 = Real.sin (Real.pi * x) ^ 2 at hp
  have hyL2 : (1 : ℝ) / 4 ≤ 2 * y := by linarith only [hyL]
  have hlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hyL2 2
  norm_num at hlo
  exact hp ▸ hlo.trans hsq

theorem finiteSineEnergy_phase_window_lower (R : Finset ℕ) (f : ℕ → ℝ)
    (z : ℤ) (hphase : ∀ n ∈ R, (z : ℝ) + 1 / 8 ≤ f n ∧ f n ≤ (z : ℝ) + 1 / 4) :
    (R.card : ℝ) / 16 ≤ finiteSineEnergy R f := by
  calc
    _ = ∑ _n ∈ R, (1 : ℝ) / 16 := by simp [div_eq_mul_inv]
    _ ≤ _ := Finset.sum_le_sum (fun n hn =>
      sine_square_lower_on_phase_window (f n) z (hphase n hn).1 (hphase n hn).2)

/-- A real phase window contributes at least its length divided by 32,
provided all its natural points are among the available bases. -/
theorem naturalWindow_energy_lower (R : Finset ℕ) (f : ℕ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hlen : 2 ≤ b - a) (hsub : naturalWindow a b ⊆ R)
    (z : ℤ) (hphase : ∀ n ∈ naturalWindow a b,
      (z : ℝ) + 1 / 8 ≤ f n ∧ f n ≤ (z : ℝ) + 1 / 4) :
    (b - a) / 32 ≤ finiteSineEnergy R f := by
  have hc := naturalWindow_card_half_length a b ha hlen
  have he := finiteSineEnergy_phase_window_lower (naturalWindow a b) f z hphase
  have hm := finiteSineEnergy_mono (naturalWindow a b) R hsub f
  linarith

end Erdos345
