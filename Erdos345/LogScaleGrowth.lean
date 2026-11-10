import Erdos345.QuasipolynomialPrefixGrowth
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Erdos345

open Filter
open scoped Topology

theorem tendsto_logScale_atTop : Tendsto logScale atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := eventually_logScale_ge b
  exact eventually_atTop.mpr ⟨N, hN⟩

theorem exp_logScale (k : ℕ) (hk : 0 < k) :
    Real.exp (logScale k) = 2 * Real.exp 1 * (k : ℝ) := by
  unfold logScale
  rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < ((2 * k : ℕ) : ℝ))]
  push_cast
  ring

theorem logScale_pow_div_identity (k n : ℕ) (hk : 0 < k) :
    logScale k ^ n / (k : ℝ) =
      (2 * Real.exp 1) * (logScale k ^ n * Real.exp (-logScale k)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [Real.exp_neg, exp_logScale k hk]
  field_simp

theorem tendsto_logScale_pow_div (n : ℕ) :
    Tendsto (fun k : ℕ => logScale k ^ n / (k : ℝ)) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp tendsto_logScale_atTop
  have hm := ht.const_mul (2 * Real.exp 1)
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (logScale_pow_div_identity k n (by omega)).symm

/-- Every fixed logarithmic power, with any fixed coefficient, is
eventually smaller than an arbitrary positive multiple of the degree. -/
theorem eventually_logScale_pow_small (n : ℕ) (C D : ℝ) (hD : 0 < D) :
    ∀ᶠ k : ℕ in atTop, C * logScale k ^ n ≤ D * (k : ℝ) := by
  have ht := (tendsto_logScale_pow_div n).const_mul C
  simp only [mul_zero] at ht
  have he := ht.eventually (gt_mem_nhds hD)
  filter_upwards [he, eventually_ge_atTop 1] with k hk hk1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hratio : C * logScale k ^ n / (k : ℝ) < D := by
    convert hk using 1
    ring
  exact ((div_lt_iff₀ hkR).mp hratio).le

theorem eventually_sixth_power_below_eighth (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C * logScale k ^ 6 ≤ logScale k ^ 8 / 4 := by
  obtain ⟨N, hN⟩ := eventually_logScale_ge (max 1 (4 * C))
  filter_upwards [eventually_ge_atTop N] with k hk
  have hK1 : 1 ≤ logScale k := (le_max_left _ _).trans (hN k hk)
  have hKC : 4 * C ≤ logScale k := (le_max_right _ _).trans (hN k hk)
  have hK2 : 4 * C ≤ logScale k ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hK2 (pow_nonneg (by linarith : 0 ≤ logScale k) 6)
  have hp : logScale k ^ 6 * logScale k ^ 2 = logScale k ^ 8 := by ring
  rw [hp] at hm
  nlinarith

end Erdos345
