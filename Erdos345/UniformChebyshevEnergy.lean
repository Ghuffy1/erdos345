import Erdos345.WeightedIntervalLower

namespace Erdos345

open Finset Polynomial MeasureTheory intervalIntegral

noncomputable def shiftedChebyshevSeries {D : ℕ} (c : Fin D → ℂ) (x : ℝ) : ℂ :=
  ∑ j, c j * (shiftedChebyshev ℂ (j : ℕ)).eval (x : ℂ)

theorem shiftedChebyshevSeries_eq {D : ℕ} (c : Fin D → ℂ) (x : ℝ) :
    shiftedChebyshevSeries c x = chebyshevSeries c (2 * x - 1) := by
  unfold shiftedChebyshevSeries chebyshevSeries
  apply sum_congr rfl
  intro j _
  rw [shiftedChebyshev_complex_eval, shiftedChebyshev_eval]

theorem integral_cos_sine_substitution (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ θ in (0 : ℝ)..Real.pi, g (Real.cos θ) * Real.sin θ) =
      ∫ x in (-1 : ℝ)..1, g x := by
  have h := integral_comp_mul_deriv (a := (0 : ℝ)) (b := Real.pi)
    (f := Real.cos) (f' := fun θ => -Real.sin θ) (g := g)
    (fun θ _ => Real.hasDerivAt_cos θ) (by fun_prop) hg
  simp only [Function.comp_apply, Real.cos_zero, Real.cos_pi] at h
  have hfun : (fun θ => g (Real.cos θ) * -Real.sin θ) =
      (fun θ => -(g (Real.cos θ) * Real.sin θ)) := by funext θ; ring
  rw [hfun, intervalIntegral.integral_neg, integral_symm (a := (-1 : ℝ)) (b := 1)] at h
  exact neg_injective h

theorem shiftedChebyshevSeries_integral_norm_sq {D : ℕ} (c : Fin D → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖shiftedChebyshevSeries c x‖ ^ 2) =
      (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, ‖chebyshevSeries c x‖ ^ 2 := by
  simp_rw [shiftedChebyshevSeries_eq]
  have h := integral_comp_mul_sub (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun x => ‖chebyshevSeries c x‖ ^ 2) (by norm_num : (2 : ℝ) ≠ 0) 1
  norm_num at h ⊢
  exact h

/-- Uniform-measure coercivity of the shifted Chebyshev basis. The loss is
polynomial in the dimension and is enough for the long-interval argument. -/
theorem shiftedChebyshevSeries_continuous_energy_lower {D : ℕ} (hD : 0 < D) (c : Fin D → ℂ) :
    Real.pi / (32 * (D : ℝ)) * (∑ j, ‖c j‖ ^ 2) ≤
      ∫ x in (0 : ℝ)..1, ‖shiftedChebyshevSeries c x‖ ^ 2 := by
  have hg : Continuous (fun x => ‖chebyshevSeries c x‖ ^ 2) := by
    unfold chebyshevSeries
    fun_prop
  have h := cosineSeries_sine_energy_lower hD c
  rw [integral_cos_sine_substitution _ hg] at h
  rw [shiftedChebyshevSeries_integral_norm_sq]
  have hhalf := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert hhalf using 1
  ring

end Erdos345
