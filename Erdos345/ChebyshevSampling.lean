import Erdos345.RiemannSampling

namespace Erdos345

open Finset Polynomial MeasureTheory

noncomputable def chebyshevCoefficientMass {D : ℕ} (c : Fin D → ℂ) : ℝ := ∑ j, ‖c j‖

theorem chebyshevCoefficientMass_nonneg {D : ℕ} (c : Fin D → ℂ) :
    0 ≤ chebyshevCoefficientMass c := sum_nonneg (fun _ _ => norm_nonneg _)

theorem chebyshevCoefficientMass_sq_le {D : ℕ} (c : Fin D → ℂ) :
    chebyshevCoefficientMass c ^ 2 ≤ (D : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin D))
    (fun _ => (1 : ℝ)) (fun j => ‖c j‖)
  simpa only [chebyshevCoefficientMass, one_mul, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using h

theorem shiftedChebyshevSeries_norm_le {D : ℕ} (c : Fin D → ℂ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖shiftedChebyshevSeries c x‖ ≤ chebyshevCoefficientMass c := by
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro j _
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (shiftedChebyshev_complex_norm_le j hx)

theorem shiftedChebyshevSeries_difference_le {D : ℕ} (c : Fin D → ℂ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ‖shiftedChebyshevSeries c x - shiftedChebyshevSeries c y‖ ≤
      2 * (D : ℝ) ^ 2 * chebyshevCoefficientMass c * |x - y| := by
  unfold shiftedChebyshevSeries
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖c j * (shiftedChebyshev ℂ j).eval (x : ℂ) -
        c j * (shiftedChebyshev ℂ j).eval (y : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * (2 * (D : ℝ) ^ 2 * |x - y|) := by
      apply sum_le_sum
      intro j _
      rw [← mul_sub, norm_mul, shiftedChebyshev_complex_eval, shiftedChebyshev_complex_eval,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have h := shiftedChebyshev_real_difference_le (j : ℕ) hy hx
      have hj : (j : ℝ) ≤ D := by exact_mod_cast j.isLt.le
      have hsq : (j : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg j.val (α := ℝ)]
      have hmul := mul_le_mul_of_nonneg_right hsq (abs_nonneg (x - y))
      nlinarith
    _ = _ := by rw [← sum_mul]; unfold chebyshevCoefficientMass; ring

theorem norm_sq_difference_le (u v : ℂ) (B : ℝ)
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * B * ‖u - v‖ := by
  have hsum : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have heq : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  rw [heq, abs_mul, abs_of_nonneg hsum]
  have h := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v) hsum
  have h' := mul_le_mul_of_nonneg_left (show ‖u‖ + ‖v‖ ≤ 2 * B by linarith) (norm_nonneg (u - v))
  nlinarith

theorem shiftedChebyshevSeries_norm_sq_difference_le {D : ℕ} (c : Fin D → ℂ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |‖shiftedChebyshevSeries c x‖ ^ 2 - ‖shiftedChebyshevSeries c y‖ ^ 2| ≤
      4 * (D : ℝ) ^ 2 * chebyshevCoefficientMass c ^ 2 * |x - y| := by
  have h := norm_sq_difference_le _ _ (chebyshevCoefficientMass c)
    (shiftedChebyshevSeries_norm_le c hx) (shiftedChebyshevSeries_norm_le c hy)
  have h' := mul_le_mul_of_nonneg_left (shiftedChebyshevSeries_difference_le c hx hy)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (chebyshevCoefficientMass_nonneg c))
  nlinarith

theorem shiftedChebyshevSeries_sampling_error {D : ℕ} (c : Fin D → ℂ) (L : ℕ) (hL : 0 < L) :
    |(1 / (L : ℝ)) * (∑ n ∈ range L, ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2) -
        ∫ x in (0 : ℝ)..1, ‖shiftedChebyshevSeries c x‖ ^ 2| ≤
      (4 * (D : ℝ) ^ 2 * chebyshevCoefficientMass c ^ 2) / L := by
  have hf : Continuous (fun x => ‖shiftedChebyshevSeries c x‖ ^ 2) := by
    unfold shiftedChebyshevSeries
    fun_prop
  simpa only [Real.norm_eq_abs, smul_eq_mul] using uniform_sampling_error_le _ hf
    (4 * (D : ℝ) ^ 2 * chebyshevCoefficientMass c ^ 2) (by positivity)
    (fun x hx y hy => by
      rw [Real.norm_eq_abs]
      exact shiftedChebyshevSeries_norm_sq_difference_le c hx hy) L hL

theorem shiftedChebyshevSeries_sampled_energy_lower {D : ℕ} (hD : 0 < D)
    (c : Fin D → ℂ) (L : ℕ) (hL : 0 < L) :
    (Real.pi / (32 * (D : ℝ)) - 4 * (D : ℝ) ^ 3 / L) * (∑ j, ‖c j‖ ^ 2) ≤
      (1 / (L : ℝ)) * ∑ n ∈ range L, ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2 := by
  have herror := (abs_le.mp (shiftedChebyshevSeries_sampling_error c L hL)).1
  have hlow := shiftedChebyshevSeries_continuous_energy_lower hD c
  have hB := mul_le_mul_of_nonneg_left (chebyshevCoefficientMass_sq_le c)
    (by positivity : 0 ≤ 4 * (D : ℝ) ^ 2 / L)
  ring_nf at herror hlow hB ⊢
  nlinarith

theorem shiftedChebyshevSeries_sampled_half_energy_lower {D : ℕ} (hD : 0 < D)
    (c : Fin D → ℂ) (L : ℕ) (hL : 0 < L)
    (hlarge : 256 * (D : ℝ) ^ 4 ≤ Real.pi * L) :
    Real.pi / (64 * (D : ℝ)) * (∑ j, ‖c j‖ ^ 2) ≤
      (1 / (L : ℝ)) * ∑ n ∈ range L, ‖shiftedChebyshevSeries c ((n : ℝ) / L)‖ ^ 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have he : 4 * (D : ℝ) ^ 3 / L ≤ Real.pi / (64 * (D : ℝ)) := by
    apply (div_le_div_iff₀ hLR (by positivity : 0 < 64 * (D : ℝ))).mpr
    nlinarith [hlarge]
  have h := shiftedChebyshevSeries_sampled_energy_lower hD c L hL
  have hcoef : Real.pi / (64 * (D : ℝ)) ≤
      Real.pi / (32 * (D : ℝ)) - 4 * (D : ℝ) ^ 3 / L := by
    have hp : Real.pi / (32 * (D : ℝ)) = 2 * (Real.pi / (64 * (D : ℝ))) := by ring
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef (sum_nonneg (fun _ _ => sq_nonneg _))).trans h

end Erdos345
