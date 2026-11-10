import Erdos345.ChebyshevOrthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Erdos345

open MeasureTheory intervalIntegral

theorem integral_split_three (f : ℝ → ℝ) (hf : Continuous f) (a b c d : ℝ) :
    (∫ x in a..d, f x) =
      (∫ x in a..b, f x) + (∫ x in b..c, f x) + (∫ x in c..d, f x) := by
  rw [integral_add_adjacent_intervals (hf.intervalIntegrable a b) (hf.intervalIntegrable b c),
    integral_add_adjacent_intervals (hf.intervalIntegrable a c) (hf.intervalIntegrable c d)]

theorem sin_lower_on_trimmed_interval {δ x : ℝ} (hδ : 0 ≤ δ)
    (hx : x ∈ Set.Icc δ (Real.pi - δ)) : 2 * δ / Real.pi ≤ Real.sin x := by
  have hx0 : 0 ≤ x := hδ.trans hx.1
  have hxpi : x ≤ Real.pi := by linarith [hx.2]
  by_cases hhalf : x ≤ Real.pi / 2
  · calc
      _ ≤ 2 / Real.pi * x := by
        have h := mul_le_mul_of_nonneg_left hx.1 (by positivity : 0 ≤ 2 / Real.pi)
        calc
          _ = 2 / Real.pi * δ := by ring
          _ ≤ _ := h
      _ ≤ _ := Real.mul_le_sin hx0 hhalf
  · have hrange : 0 ≤ Real.pi - x ∧ Real.pi - x ≤ Real.pi / 2 := by constructor <;> linarith
    calc
      _ ≤ 2 / Real.pi * (Real.pi - x) := by
        have h := mul_le_mul_of_nonneg_left (show δ ≤ Real.pi - x by linarith [hx.2])
          (by positivity : 0 ≤ 2 / Real.pi)
        calc
          _ = 2 / Real.pi * δ := by ring
          _ ≤ _ := h
      _ ≤ Real.sin (Real.pi - x) := Real.mul_le_sin hrange.1 hrange.2
      _ = _ := Real.sin_pi_sub x

/-- Removing two short endpoint intervals bounds the loss before weighting
by sine. All continuity, sign and endpoint hypotheses are explicit. -/
theorem sine_weighted_integral_lower (f : ℝ → ℝ) (hf : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x) (B δ : ℝ)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ Real.pi / 2)
    (hbound : ∀ x ∈ Set.Icc 0 Real.pi, f x ≤ B) :
    ((∫ x in (0 : ℝ)..Real.pi, f x) - 2 * δ * B) * (2 * δ / Real.pi) ≤
      ∫ x in (0 : ℝ)..Real.pi, f x * Real.sin x := by
  have hmiddle : δ ≤ Real.pi - δ := by linarith
  have hright : Real.pi - δ ≤ Real.pi := by linarith
  have hleftpi : δ ≤ Real.pi := by linarith [Real.pi_pos]
  have hleft : (∫ x in (0 : ℝ)..δ, f x) ≤ δ * B := by
    calc
      _ ≤ ∫ _x in (0 : ℝ)..δ, B := integral_mono_on hδ (hf.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun x hx => hbound x ⟨hx.1, hx.2.trans hleftpi⟩)
      _ = _ := by simp
  have htail : (∫ x in (Real.pi - δ)..Real.pi, f x) ≤ δ * B := by
    calc
      _ ≤ ∫ _x in (Real.pi - δ)..Real.pi, B := integral_mono_on hright (hf.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) (fun x hx => hbound x ⟨by linarith [hx.1], hx.2⟩)
      _ = _ := by simp
  have hsplit := integral_split_three f hf 0 δ (Real.pi - δ) Real.pi
  have hmass : (∫ x in (0 : ℝ)..Real.pi, f x) - 2 * δ * B ≤
      ∫ x in δ..(Real.pi - δ), f x := by linarith
  have hw : Continuous (fun x => f x * Real.sin x) := hf.mul Real.continuous_sin
  have hleftw : 0 ≤ ∫ x in (0 : ℝ)..δ, f x * Real.sin x :=
    integral_nonneg hδ (fun x hx => mul_nonneg (hnonneg x)
      (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (hx.2.trans hleftpi)))
  have hrightw : 0 ≤ ∫ x in (Real.pi - δ)..Real.pi, f x * Real.sin x :=
    integral_nonneg hright (fun x hx => mul_nonneg (hnonneg x)
      (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1]) hx.2))
  have hsplitw := integral_split_three (fun x => f x * Real.sin x) hw 0 δ (Real.pi - δ) Real.pi
  have hmidw : (2 * δ / Real.pi) * (∫ x in δ..(Real.pi - δ), f x) ≤
      ∫ x in δ..(Real.pi - δ), f x * Real.sin x := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hmiddle ((continuous_const.mul hf).intervalIntegrable _ _) (hw.intervalIntegrable _ _)
    intro x hx
    have h := mul_le_mul_of_nonneg_left (sin_lower_on_trimmed_interval hδ hx) (hnonneg x)
    change (2 * δ / Real.pi) * f x ≤ f x * Real.sin x
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 2 * δ / Real.pi)
  nlinarith

theorem cosineSeries_sine_energy_lower {D : ℕ} (hD : 0 < D) (c : Fin D → ℂ) :
    Real.pi / (16 * (D : ℝ)) * (∑ j, ‖c j‖ ^ 2) ≤
      ∫ θ in (0 : ℝ)..Real.pi, ‖chebyshevSeries c (Real.cos θ)‖ ^ 2 * Real.sin θ := by
  let S : ℝ := ∑ j, ‖c j‖ ^ 2
  let δ := Real.pi / (8 * (D : ℝ))
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ Real.pi / 2 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by nlinarith)
  have hf : Continuous (fun θ => ‖chebyshevSeries c (Real.cos θ)‖ ^ 2) := by
    unfold chebyshevSeries
    fun_prop
  have h := sine_weighted_integral_lower _ hf (fun θ => sq_nonneg _) ((D : ℝ) * S) δ hδ hδhalf
    (fun θ _ => chebyshevSeries_pointwise_sq_le c (Real.abs_cos_le_one θ))
  have hlow := cosineSeries_energy_lower c
  have hc : 2 * δ / Real.pi = 1 / (4 * (D : ℝ)) := by
    dsimp [δ]
    field_simp
    ring
  have hloss : 2 * δ * ((D : ℝ) * S) = Real.pi / 4 * S := by
    dsimp [δ]
    field_simp
    ring
  rw [hc, hloss] at h
  have hcmp := mul_le_mul_of_nonneg_right hlow (by positivity : 0 ≤ 1 / (4 * (D : ℝ)))
  change Real.pi / 2 * S * (1 / (4 * (D : ℝ))) ≤ _ at hcmp
  have heq : Real.pi / (16 * (D : ℝ)) * S =
      (Real.pi / 2 * S - Real.pi / 4 * S) * (1 / (4 * (D : ℝ))) := by ring
  rw [heq]
  nlinarith

end Erdos345
