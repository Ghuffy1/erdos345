import Erdos345.PowerWindowPopulation
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Erdos345

theorem reciprocal_window_sum (Y : ℕ) :
    (∑ j ∈ Finset.Icc 1 Y, 1 / ((j : ℝ) + 1)) = (harmonic (Y + 1) : ℝ) - 1 := by
  induction Y with
  | zero => simp [harmonic]
  | succ Y ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ (Y + 1)]
    push_cast
    ring

theorem reciprocal_window_sum_log_lower (Y : ℕ) :
    Real.log ((Y : ℝ) + 2) - 1 ≤ ∑ j ∈ Finset.Icc 1 Y, 1 / ((j : ℝ) + 1) := by
  rw [reciprocal_window_sum]
  have h := log_add_one_le_harmonic (Y + 1)
  push_cast at h
  have he : (Y : ℝ) + 1 + 1 = (Y : ℝ) + 2 := by ring
  rw [he] at h
  linarith

theorem powerWindows_log_energy_lower (R : Finset ℕ) (A U k Y : ℕ) (hk : 0 < k)
    (r : ℝ) (hr : 0 < r)
    (hsize : 16 * (k : ℝ) * ((Y : ℝ) + 1) ≤ r)
    (hA : (A : ℝ) ≤ r) (hU : r * ((Y : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ U)
    (hpopulation : Finset.Icc A U ⊆ R) :
    r / (256 * (k : ℝ)) * (Real.log ((Y : ℝ) + 2) - 1) ≤
      finiteSineEnergy R (fun n => ((n : ℝ) / r) ^ k) := by
  exact (mul_le_mul_of_nonneg_left (reciprocal_window_sum_log_lower Y) (by positivity)).trans
    (powerWindows_energy_lower R A U k Y hk r hr hsize hA hU hpopulation)

end Erdos345
