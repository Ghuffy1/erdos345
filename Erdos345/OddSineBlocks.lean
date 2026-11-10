import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace Erdos345

noncomputable def oddSineSum (M : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, Real.sin ((2 * (i : ℝ) + 1) * x)

theorem oddSineSum_identity (M : ℕ) (x : ℝ) :
    Real.sin x * oddSineSum M x = Real.sin ((M : ℝ) * x) ^ 2 := by
  have h := Real.sin_mul_sum_sin M (2 * x) x
  have hsum : (∑ i ∈ Finset.range M, Real.sin (2 * x * (i : ℝ) + x)) = oddSineSum M x := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [hsum] at h
  have h1 : 2 * x / 2 = x := by ring
  have h2 : (M : ℝ) * (2 * x) / 2 = (M : ℝ) * x := by ring
  have h3 : ((M : ℝ) - 1) * (2 * x) / 2 + x = (M : ℝ) * x := by ring
  rw [h1, h2, h3] at h
  nlinarith only [h]

theorem oddSineSum_abs_le (M : ℕ) (x : ℝ) : |oddSineSum M x| ≤ M := by
  calc
    _ ≤ ∑ i ∈ Finset.range M, |Real.sin ((2 * (i : ℝ) + 1) * x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum (fun i _ => Real.abs_sin_le_one _)
    _ = _ := by simp

theorem oddSineSum_zero (M : ℕ) : oddSineSum M 0 = 0 := by simp [oddSineSum]

theorem oddSineSum_pi (M : ℕ) : oddSineSum M Real.pi = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have heq : (2 * (i : ℝ) + 1) * Real.pi = ((2 * i + 1 : ℕ) : ℝ) * Real.pi := by push_cast; ring
  rw [heq, Real.sin_nat_mul_pi]

theorem oddSineSum_abs_le_inv_sin (M : ℕ) (x : ℝ) (hx : Real.sin x ≠ 0) :
    |oddSineSum M x| ≤ 1 / |Real.sin x| := by
  have hid := congrArg abs (oddSineSum_identity M x)
  simp only [abs_mul, abs_pow] at hid
  have hnum := Real.abs_sin_le_one ((M : ℝ) * x)
  have hnum0 := abs_nonneg (Real.sin ((M : ℝ) * x))
  apply (le_div_iff₀ (abs_pos.mpr hx)).mpr
  nlinarith

theorem oddSineSum_nonneg (M : ℕ) {x : ℝ} (hx : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ oddSineSum M x := by
  by_cases h0 : x = 0
  · rw [h0, oddSineSum_zero]
  by_cases hπ : x = Real.pi
  · rw [hπ, oddSineSum_pi]
  have hs := Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne hx (Ne.symm h0)) (lt_of_le_of_ne hxπ hπ)
  have hid := oddSineSum_identity M x
  nlinarith [sq_nonneg (Real.sin ((M : ℝ) * x))]

theorem oddSineSum_small_angle_lower (M : ℕ) (hM : 1 ≤ M) {x : ℝ}
    (hx : 0 < x) (hsmall : (M : ℝ) * x ≤ Real.pi / 2) :
    4 / Real.pi ^ 2 * (M : ℝ) ^ 2 * x ≤ oddSineSum M x := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMx : 0 ≤ (M : ℝ) * x := mul_nonneg (by positivity) hx.le
  have hxπ : x ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hsum := oddSineSum_nonneg M hx.le hxπ
  have hsx := Real.sin_le hx.le
  have hnum := Real.mul_le_sin hMx hsmall
  have hnum0 : 0 ≤ 2 / Real.pi * ((M : ℝ) * x) := by positivity
  have hsquare : (2 / Real.pi * ((M : ℝ) * x)) ^ 2 ≤ Real.sin ((M : ℝ) * x) ^ 2 := by
    nlinarith
  have hmult := mul_le_mul_of_nonneg_right hsx hsum
  have hid := oddSineSum_identity M x
  have halg : (2 / Real.pi * ((M : ℝ) * x)) ^ 2 =
      (4 / Real.pi ^ 2 * (M : ℝ) ^ 2 * x) * x := by
    field_simp
    ring
  rw [halg] at hsquare
  apply (mul_le_mul_iff_left₀ hx).mp
  nlinarith only [hsquare, hmult, hid]

end Erdos345
