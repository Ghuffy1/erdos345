import Erdos345.PowerWindowGeometry

namespace Erdos345

theorem rpow_increment_lower_small (x y p : ℝ) (hx : 0 < x) (hxy : x < y)
    (hy : y ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (y - x) ≤ y ^ p - x ^ p := by
  have hy0 : 0 < y := hx.trans hxy
  have hs := (Real.concaveOn_rpow hp0 hp1).le_slope_of_hasDerivAt hx.le hy0.le hxy
    (Real.hasDerivAt_rpow_const (Or.inl hy0.ne'))
  rw [slope_def_field] at hs
  have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
  have hyPow : 1 ≤ y ^ (p - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy (by linarith)
  have hc := mul_le_mul_of_nonneg_left hyPow hp0
  have hc' := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hxy.le)
  nlinarith only [hm, hc']

theorem firstPowerWindow_length_lower (r : ℝ) (hr : 0 ≤ r) (k : ℕ) (hk : 0 < k) :
    r / (8 * (k : ℝ)) ≤ powerWindowUpper r k 0 - powerWindowLower r k 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := rpow_increment_lower_small (1 / 8) (1 / 4) ((k : ℝ)⁻¹)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) (inv_le_one_of_one_le₀ hk1)
  have hm := mul_le_mul_of_nonneg_left h hr
  simp only [powerWindowUpper, powerWindowLower, Nat.cast_zero, zero_add]
  convert hm using 1 <;> ring

theorem firstPowerWindow_lower_ge (r : ℝ) (hr : 0 ≤ r) (k : ℕ) (hk : 0 < k) :
    r / 8 ≤ powerWindowLower r k 0 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1 / 8 : ℝ) ≤ (1 / 8 : ℝ) ^ ((k : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1) (inv_le_one_of_one_le₀ hk1)
    simpa only [Real.rpow_one] using h
  have hm := mul_le_mul_of_nonneg_left hp hr
  simpa only [powerWindowLower, Nat.cast_zero, zero_add, mul_one_div] using hm

theorem firstPowerWindow_energy_lower (R : Finset ℕ) (A U k : ℕ) (hk : 0 < k)
    (r : ℝ) (hr : 0 < r) (hsize : 16 * (k : ℝ) ≤ r)
    (hA : (A : ℝ) ≤ r / 8) (hU : r * (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) ≤ U)
    (hpopulation : Finset.Icc A U ⊆ R) :
    r / (256 * (k : ℝ)) ≤ finiteSineEnergy R (fun n => ((n : ℝ) / r) ^ k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlen := firstPowerWindow_length_lower r hr.le k hk
  have hlen2 : 2 ≤ powerWindowUpper r k 0 - powerWindowLower r k 0 := by
    have hd : 0 < 8 * (k : ℝ) := by positivity
    have h : 2 ≤ r / (8 * (k : ℝ)) := (le_div_iff₀ hd).mpr (by linarith)
    exact h.trans hlen
  have hsub : naturalWindow (powerWindowLower r k 0) (powerWindowUpper r k 0) ⊆ R := by
    intro n hn
    have hb : 0 ≤ powerWindowUpper r k 0 := by unfold powerWindowUpper; positivity
    obtain ⟨hl, hu⟩ := (mem_naturalWindow _ _ hb n).mp hn
    have hnA : (A : ℝ) ≤ n := hA.trans ((firstPowerWindow_lower_ge r hr.le k hk).trans hl)
    have hnU : (n : ℝ) ≤ U := by
      have htop : powerWindowUpper r k 0 ≤ U := by
        simpa only [powerWindowUpper, Nat.cast_zero, zero_add] using hU
      exact hu.trans htop
    exact hpopulation (Finset.mem_Icc.mpr ⟨by exact_mod_cast hnA, by exact_mod_cast hnU⟩)
  have hphase : ∀ n ∈ naturalWindow (powerWindowLower r k 0) (powerWindowUpper r k 0),
      (0 : ℝ) + 1 / 8 ≤ ((n : ℝ) / r) ^ k ∧ ((n : ℝ) / r) ^ k ≤ 0 + 1 / 4 := by
    intro n hn
    simpa only [Nat.cast_zero] using powerWindow_phase r hr k 0 n hk hn
  have he := naturalWindow_energy_lower R (fun n => ((n : ℝ) / r) ^ k)
    (powerWindowLower r k 0) (powerWindowUpper r k 0)
    (powerWindowLower_nonneg r hr.le k 0) hlen2 hsub 0 (by simpa only [Int.cast_zero] using hphase)
  have hd := div_le_div_of_nonneg_right hlen (by norm_num : (0 : ℝ) ≤ 32)
  have hf := hd.trans he
  convert hf using 1
  ring

theorem large_scale_energy_lower (R : Finset ℕ) (A U N k : ℕ) (hk : 0 < k)
    (r : ℝ) (hrN : (N : ℝ) / 2 ≤ r) (hrtop : r ≤ N)
    (hNk : 32 * (k : ℝ) ≤ N) (hNA : 16 * (A : ℝ) ≤ N)
    (hU : (N : ℝ) * (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) ≤ U)
    (hpopulation : Finset.Icc A U ⊆ R) :
    (N : ℝ) / (512 * (k : ℝ)) ≤ finiteSineEnergy R (fun n => ((n : ℝ) / r) ^ k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : 0 < r := by linarith
  have hsize : 16 * (k : ℝ) ≤ r := by linarith
  have hA : (A : ℝ) ≤ r / 8 := by linarith
  have htop : r * (1 / 4 : ℝ) ^ ((k : ℝ)⁻¹) ≤ U :=
    (mul_le_mul_of_nonneg_right hrtop (Real.rpow_nonneg (by norm_num) _)).trans hU
  have he := firstPowerWindow_energy_lower R A U k hk r hr hsize hA htop hpopulation
  have hcmp : (N : ℝ) / (512 * (k : ℝ)) ≤ r / (256 * (k : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hrN, hkR]
  exact hcmp.trans he

end Erdos345
