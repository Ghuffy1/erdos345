import Erdos345.CosineFlatSupNorm
import Mathlib.Analysis.Polynomial.Fourier

namespace Erdos345

open Finset Polynomial

theorem complex_coefficient_norm_le_unit_bound (p : ℂ[X]) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) (j : ℕ) : ‖p.coeff j‖ ≤ M := by
  have hf : CircleIntegrable (fun z : ℂ => ‖p.eval z‖ ^ 2) 0 1 :=
    (p.continuous.norm.pow 2).continuousOn.circleIntegrable'
  have havg : Real.circleAverage (fun z : ℂ => ‖p.eval z‖ ^ 2) 0 1 ≤ M ^ 2 := by
    apply Real.circleAverage_mono_on_of_le_circle hf
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using hz
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz1) 2
  rw [← p.sum_sq_norm_coeff_eq_circleAverage] at havg
  by_cases hj : p.coeff j = 0
  · simpa only [hj, norm_zero] using hM
  · have hmem : j ∈ p.support := mem_support_iff.mpr hj
    have hterm : ‖p.coeff j‖ ^ 2 ≤ ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 :=
      single_le_sum (fun i _ => sq_nonneg ‖p.coeff i‖) hmem
    have hn : 0 ≤ ‖p.coeff j‖ := norm_nonneg _
    nlinarith

theorem coefficientL1_le_unit_bound (p : ℤ[X]) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, ‖z‖ = 1 → ‖(p.map (Int.castRingHom ℂ)).eval z‖ ≤ M) :
    coefficientL1 p ≤ ((p.natDegree : ℝ) + 1) * M := by
  unfold coefficientL1
  calc
    _ ≤ ∑ _i ∈ range (p.natDegree + 1), M := by
      apply sum_le_sum
      intro i _
      have h := complex_coefficient_norm_le_unit_bound (p.map (Int.castRingHom ℂ)) M hM hbound i
      simpa only [coeff_map, Int.coe_castRingHom, Complex.norm_intCast] using h
    _ = _ := by simp

theorem coefficientL1_flat_from_cosine (N : ℕ) (w : ℕ → ℕ) (a : ℝ)
    (hcos : flatCosineNonnegative N w a) (hJ : 0 < weightMass N w) :
    coefficientL1 (flatPolynomial N w) ≤
      ((N : ℝ) * weightMass N w + 1) * Real.exp (1 + a * Real.log (weightMass N w : ℝ)) := by
  have h := coefficientL1_le_unit_bound (flatPolynomial N w)
    (Real.exp (1 + a * Real.log (weightMass N w : ℝ))) (Real.exp_pos _).le
    (fun z hz => flatPolynomial_sup_norm_mass_bound N w a hcos hJ z hz)
  have hdegree : ((flatPolynomial N w).natDegree : ℝ) ≤ (N : ℝ) * weightMass N w := by
    exact_mod_cast flatPolynomial_natDegree_le N w
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end Erdos345
