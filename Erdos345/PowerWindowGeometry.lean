import Erdos345.StackedWindowEnergy
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Erdos345

theorem rpow_increment_lower (x y p : ℝ) (hx : 0 < x) (hxy : x < y)
    (hy : 1 ≤ y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (y - x) / y ≤ y ^ p - x ^ p := by
  have hy0 : 0 < y := hx.trans hxy
  have hs := (Real.concaveOn_rpow hp0 hp1).le_slope_of_hasDerivAt hx.le hy0.le hxy
    (Real.hasDerivAt_rpow_const (Or.inl hy0.ne'))
  rw [slope_def_field] at hs
  have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
  have hyPow : 1 ≤ y ^ p := Real.one_le_rpow hy hp0
  have hc : p / y ≤ p * y ^ (p - 1) := by
    rw [Real.rpow_sub_one hy0.ne']
    calc
      p / y = p * (1 / y) := by ring
      _ ≤ p * (y ^ p / y) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hyPow hy0.le) hp0
  calc
    p * (y - x) / y = (p / y) * (y - x) := by ring
    _ ≤ (p * y ^ (p - 1)) * (y - x) :=
      mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hxy.le)
    _ ≤ _ := hm

noncomputable def powerWindowLower (r : ℝ) (k j : ℕ) : ℝ :=
  r * ((j : ℝ) + 1 / 8) ^ ((k : ℝ)⁻¹)

noncomputable def powerWindowUpper (r : ℝ) (k j : ℕ) : ℝ :=
  r * ((j : ℝ) + 1 / 4) ^ ((k : ℝ)⁻¹)

theorem powerWindowLower_nonneg (r : ℝ) (hr : 0 ≤ r) (k j : ℕ) :
    0 ≤ powerWindowLower r k j := by
  unfold powerWindowLower
  positivity

/-- The exact power-window length is bounded below uniformly in the
degree, with no growing-degree asymptotic hidden in the statement. -/
theorem powerWindow_length_lower (r : ℝ) (hr : 0 ≤ r) (k j : ℕ)
    (hk : 0 < k) (hj : 1 ≤ j) :
    r / (8 * (k : ℝ) * ((j : ℝ) + 1)) ≤
      powerWindowUpper r k j - powerWindowLower r k j := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  let p := (k : ℝ)⁻¹
  let x := (j : ℝ) + 1 / 8
  let y := (j : ℝ) + 1 / 4
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hp1 : p ≤ 1 := by dsimp only [p]; exact inv_le_one_of_one_le₀ hk1
  have hinc := rpow_increment_lower x y p (by dsimp only [x]; positivity)
    (by dsimp only [x, y]; linarith) (by dsimp only [y]; linarith) hp0 hp1
  have hd : 0 < 8 * (k : ℝ) * ((j : ℝ) + 1 / 4) := by positivity
  have hden : 8 * (k : ℝ) * ((j : ℝ) + 1 / 4) ≤
      8 * (k : ℝ) * ((j : ℝ) + 1) := by nlinarith
  have hrat : 1 / (8 * (k : ℝ) * ((j : ℝ) + 1)) ≤ p * (y - x) / y := by
    calc
      _ ≤ 1 / (8 * (k : ℝ) * ((j : ℝ) + 1 / 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hd hden
      _ = _ := by dsimp only [p, x, y]; field_simp; ring
  have hm := mul_le_mul_of_nonneg_left (hrat.trans hinc) hr
  simpa only [powerWindowUpper, powerWindowLower, mul_sub, mul_one_div] using hm

theorem powerWindow_phase (r : ℝ) (hr : 0 < r) (k j n : ℕ) (hk : 0 < k)
    (hn : n ∈ naturalWindow (powerWindowLower r k j) (powerWindowUpper r k j)) :
    (j : ℝ) + 1 / 8 ≤ ((n : ℝ) / r) ^ k ∧
      ((n : ℝ) / r) ^ k ≤ (j : ℝ) + 1 / 4 := by
  have hb : 0 ≤ powerWindowUpper r k j := by unfold powerWindowUpper; positivity
  obtain ⟨hl, hu⟩ := (mem_naturalWindow _ _ hb n).mp hn
  have hlo : ((j : ℝ) + 1 / 8) ^ ((k : ℝ)⁻¹) ≤ (n : ℝ) / r :=
    (le_div_iff₀ hr).mpr (by simpa only [powerWindowLower, mul_comm] using hl)
  have hup : (n : ℝ) / r ≤ ((j : ℝ) + 1 / 4) ^ ((k : ℝ)⁻¹) :=
    (div_le_iff₀ hr).mpr (by simpa only [powerWindowUpper, mul_comm] using hu)
  have hlo' := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hlo k
  have hup' := pow_le_pow_left₀ (show 0 ≤ (n : ℝ) / r by positivity) hup k
  rw [Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hk)] at hlo' hup'
  exact ⟨hlo', hup'⟩

end Erdos345
