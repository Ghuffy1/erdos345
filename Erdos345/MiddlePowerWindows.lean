import Erdos345.PowerWindowHarmonic

namespace Erdos345

noncomputable def stackWindowCount (r : ℝ) (k : ℕ) : ℕ := ⌊r / (1000 * (k : ℝ))⌋₊

theorem stackWindowCount_size (r : ℝ) (k : ℕ) (hk : 0 < k) (hr : 1000 * (k : ℝ) ≤ r) :
    16 * (k : ℝ) * ((stackWindowCount r k : ℝ) + 1) ≤ r := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hr0 : 0 ≤ r := by linarith
  have hfloor : (stackWindowCount r k : ℝ) ≤ r / (1000 * (k : ℝ)) :=
    Nat.floor_le (by positivity)
  have hm := (le_div_iff₀ (show 0 < 1000 * (k : ℝ) by positivity)).mp hfloor
  nlinarith

theorem stackWindowCount_le (r : ℝ) (k N : ℕ) (hk : 0 < k) (hr : 0 ≤ r)
    (hrN : r ≤ N) : stackWindowCount r k ≤ N := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : (1 : ℝ) ≤ 1000 * k := by linarith
  have hfloor : (stackWindowCount r k : ℝ) ≤ r / (1000 * (k : ℝ)) :=
    Nat.floor_le (by positivity)
  have h := hfloor.trans ((div_le_self hr hd).trans hrN)
  exact_mod_cast h

theorem stackWindowCount_log (r : ℝ) (k : ℕ) (hk : 0 < k) (hr : 0 < r) :
    Real.log (r / (1000 * (k : ℝ))) ≤ Real.log ((stackWindowCount r k : ℝ) + 2) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfloor : r / (1000 * (k : ℝ)) < (stackWindowCount r k : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  exact Real.log_le_log (by positivity) (by linarith)

/-- The many-window case on a population containing [A,U]. A single
root bound on N controls all actual endpoints. -/
theorem middle_scale_energy_lower (R : Finset ℕ) (A U N k : ℕ) (hk : 0 < k)
    (r : ℝ) (hr : 1000 * (k : ℝ) ≤ r) (hrN : r ≤ (N : ℝ) / 2)
    (hroot : ((N : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ 3 / 2)
    (hU : 3 * (N : ℝ) / 4 ≤ U) (hA : (A : ℝ) ≤ r)
    (hpopulation : Finset.Icc A U ⊆ R) :
    r / (256 * (k : ℝ)) * (Real.log (r / (1000 * (k : ℝ))) - 1) ≤
      finiteSineEnergy R (fun n => ((n : ℝ) / r) ^ k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hr0 : 0 < r := by linarith
  have hYN := stackWindowCount_le r k N hk hr0.le (by linarith)
  have hrootY : ((stackWindowCount r k : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ 3 / 2 := by
    apply le_trans (Real.rpow_le_rpow (by positivity) ?_ (by positivity)) hroot
    exact_mod_cast Nat.add_le_add_right hYN 1
  have htop : r * ((stackWindowCount r k : ℝ) + 1) ^ ((k : ℝ)⁻¹) ≤ U := by
    have h := mul_le_mul_of_nonneg_left hrootY hr0.le
    nlinarith
  have he := powerWindows_log_energy_lower R A U k (stackWindowCount r k) hk r hr0
    (stackWindowCount_size r k hk hr) hA htop hpopulation
  have hl := stackWindowCount_log r k hk hr0
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hl 1)
    (show 0 ≤ r / (256 * (k : ℝ)) by positivity)
  exact hm.trans he

end Erdos345
