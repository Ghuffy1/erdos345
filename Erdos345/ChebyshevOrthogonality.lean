import Erdos345.ChebyshevBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

namespace Erdos345

open Finset Polynomial MeasureTheory

theorem integral_sq_finite_sum {I A : Type*} [Fintype I] [MeasurableSpace A]
    (μ : Measure A) (v : I → A → ℝ) (c : I → ℝ)
    (hv : ∀ i j, Integrable (fun x => v i x * v j x) μ) :
    (∫ x, (∑ i, c i * v i x) ^ 2 ∂μ) =
      ∑ i, ∑ j, c i * c j * ∫ x, v i x * v j x ∂μ := by
  have hi (i j : I) : Integrable (fun x => (c i * v i x) * (c j * v j x)) μ := by
    convert (hv i j).const_mul (c i * c j) using 1
    funext x
    ring
  simp_rw [pow_two, sum_mul, mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply sum_congr rfl
  intro j _
  have heq : (fun x => (c i * v i x) * (c j * v j x)) =
      (fun x => (c i * c j) * (v i x * v j x)) := by funext x; ring
  rw [heq, integral_const_mul]

theorem integral_chebyshev_pair (i j : ℕ) :
    (∫ x, (Chebyshev.T ℝ i).eval x * (Chebyshev.T ℝ j).eval x ∂Chebyshev.measureT) =
      if i = j then (if i = 0 then Real.pi else Real.pi / 2) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    by_cases hi : i = 0
    · subst i
      simpa using Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    · rw [ite_eq_right hi]
      exact Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hi
  · rw [ite_eq_right hij]
    exact Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hij

noncomputable def chebyshevRealSeries {D : ℕ} (c : Fin D → ℝ) (x : ℝ) : ℝ :=
  ∑ j, c j * (Chebyshev.T ℝ (j : ℕ)).eval x

noncomputable def chebyshevSeries {D : ℕ} (c : Fin D → ℂ) (x : ℝ) : ℂ :=
  ∑ j, c j * Complex.ofReal ((Chebyshev.T ℝ (j : ℕ)).eval x)

theorem integral_chebyshev_realSeries_sq {D : ℕ} (c : Fin D → ℝ) :
    (∫ x, chebyshevRealSeries c x ^ 2 ∂Chebyshev.measureT) =
      ∑ j : Fin D, (if (j : ℕ) = 0 then Real.pi else Real.pi / 2) * c j ^ 2 := by
  unfold chebyshevRealSeries
  rw [integral_sq_finite_sum]
  · apply sum_congr rfl
    intro i _
    simp_rw [integral_chebyshev_pair]
    have heq (j : Fin D) : ((i : ℕ) = (j : ℕ)) ↔ i = j := Fin.val_inj
    simp_rw [heq]
    simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
    split_ifs <;> ring
  · intro i j
    exact Chebyshev.integrable_measureT (by fun_prop)

theorem chebyshevSeries_norm_sq {D : ℕ} (c : Fin D → ℂ) (x : ℝ) :
    ‖chebyshevSeries c x‖ ^ 2 =
      chebyshevRealSeries (fun j => (c j).re) x ^ 2 +
      chebyshevRealSeries (fun j => (c j).im) x ^ 2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, chebyshevSeries, chebyshevRealSeries,
    Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  ring

theorem integral_chebyshevSeries_norm_sq {D : ℕ} (c : Fin D → ℂ) :
    (∫ x, ‖chebyshevSeries c x‖ ^ 2 ∂Chebyshev.measureT) =
      ∑ j : Fin D, (if (j : ℕ) = 0 then Real.pi else Real.pi / 2) * ‖c j‖ ^ 2 := by
  simp_rw [chebyshevSeries_norm_sq]
  rw [integral_add, integral_chebyshev_realSeries_sq, integral_chebyshev_realSeries_sq,
    ← sum_add_distrib]
  · apply sum_congr rfl
    intro j _
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply]
    ring
  · exact Chebyshev.integrable_measureT (by unfold chebyshevRealSeries; fun_prop)
  · exact Chebyshev.integrable_measureT (by unfold chebyshevRealSeries; fun_prop)

theorem cosineSeries_energy_lower {D : ℕ} (c : Fin D → ℂ) :
    (Real.pi / 2) * ∑ j, ‖c j‖ ^ 2 ≤
      ∫ θ in (0 : ℝ)..Real.pi, ‖chebyshevSeries c (Real.cos θ)‖ ^ 2 := by
  rw [← Chebyshev.integral_measureT_eq_integral_cos
    (f := fun x => ‖chebyshevSeries c x‖ ^ 2), integral_chebyshevSeries_norm_sq, mul_sum]
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  split_ifs
  · linarith [Real.pi_pos]
  · exact le_rfl

theorem chebyshevSeries_pointwise_sq_le {D : ℕ} (c : Fin D → ℂ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖chebyshevSeries c x‖ ^ 2 ≤ (D : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
  have hnorm : ‖chebyshevSeries c x‖ ≤ ∑ j, ‖c j‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum ?_)
    intro j _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (Chebyshev.abs_eval_T_real_le_one (j : ℕ) hx)
  have hsq : ‖chebyshevSeries c x‖ ^ 2 ≤ (∑ j, ‖c j‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hCS := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin D))
    (fun _ => (1 : ℝ)) (fun j => ‖c j‖)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hCS
  exact hsq.trans hCS

end Erdos345
