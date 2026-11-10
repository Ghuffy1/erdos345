import Erdos345.ExponentialDomination
import Erdos345.UnreservedFrequencyBound

namespace Erdos345

noncomputable def fourierN (k : ℕ) : ℕ := ⌈Real.exp (logScale k ^ 8)⌉₊

noncomputable def fourierW (k : ℕ) : ℕ := ⌈Real.exp (logScale k ^ 8 / 2)⌉₊

noncomputable def fourierH (k : ℕ) : ℝ := 65536 * (k : ℝ) * logScale k ^ 8 + 514

noncomputable def fourierT (k : ℕ) : ℕ := fourierN k / 8192

theorem fourierN_pos (k : ℕ) : 0 < fourierN k := by
  have h : (0 : ℝ) < fourierN k := (Real.exp_pos _).trans_le (Nat.le_ceil _)
  exact_mod_cast h

theorem fourierW_pos (k : ℕ) : 0 < fourierW k := by
  have h : (0 : ℝ) < fourierW k := (Real.exp_pos _).trans_le (Nat.le_ceil _)
  exact_mod_cast h

theorem fourierW_le_N (k : ℕ) : fourierW k ≤ fourierN k := by
  apply Nat.ceil_mono
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ logScale k ^ 8 := by positivity
  linarith

theorem fourierH_nonneg (k : ℕ) : 0 ≤ fourierH k := by unfold fourierH; positivity

theorem fourierH_add_one_le (k : ℕ) (hk : 0 < k) :
    fourierH k + 1 ≤ 66051 * (k : ℝ) * logScale k ^ 8 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK8 : 1 ≤ logScale k ^ 8 := one_le_pow₀ (logScale_ge_one k hk)
  have hp : 1 ≤ (k : ℝ) * logScale k ^ 8 := by nlinarith
  unfold fourierH
  nlinarith

theorem fourierN_bounds (k : ℕ) :
    Real.exp (logScale k ^ 8) ≤ (fourierN k : ℝ) ∧
      (fourierN k : ℝ) ≤ 2 * Real.exp (logScale k ^ 8) := by
  have hA : 0 ≤ logScale k ^ 8 := by positivity
  have he : 1 ≤ Real.exp (logScale k ^ 8) := (Real.one_le_exp_iff).mpr hA
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (logScale k ^ 8)).le
  exact ⟨Nat.le_ceil _, by dsimp only [fourierN]; linarith⟩

theorem fourierW_bounds (k : ℕ) :
    Real.exp (logScale k ^ 8 / 2) ≤ (fourierW k : ℝ) ∧
      (fourierW k : ℝ) + 1 ≤ 3 * Real.exp (logScale k ^ 8 / 2) := by
  have hA : 0 ≤ logScale k ^ 8 / 2 := by positivity
  have he : 1 ≤ Real.exp (logScale k ^ 8 / 2) := (Real.one_le_exp_iff).mpr hA
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (logScale k ^ 8 / 2)).le
  exact ⟨Nat.le_ceil _, by dsimp only [fourierW]; linarith⟩

theorem log_fourierN_add_one_le (k : ℕ) :
    Real.log ((fourierN k : ℝ) + 1) ≤ logScale k ^ 8 + 2 := by
  have hA : 0 ≤ logScale k ^ 8 := by positivity
  have he : 1 ≤ Real.exp (logScale k ^ 8) := (Real.one_le_exp_iff).mpr hA
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (logScale k ^ 8)).le
  have hbound : (fourierN k : ℝ) + 1 ≤ 3 * Real.exp (logScale k ^ 8) := by
    dsimp only [fourierN]
    linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (fourierN k : ℝ) + 1) hbound
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hl
  have hlog3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith

end Erdos345
