import Erdos345.ModulatedGram
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.Calculus.MeanValue

namespace Erdos345

open Finset Polynomial

noncomputable def shiftedChebyshev (K : Type*) [Field K] (n : ℕ) : K[X] :=
  (Chebyshev.T K (n : ℤ)).comp (C 2 * X - 1)

theorem shiftedChebyshev_natDegree (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    (shiftedChebyshev K n).natDegree = n := by
  have hdeg : (C 2 * X - 1 : K[X]).natDegree = 1 := by
    simpa only [← C_1, natDegree_sub_C] using natDegree_C_mul_X (R := K) 2 (by norm_num)
  rw [shiftedChebyshev, natDegree_comp, hdeg, Chebyshev.natDegree_T,
    Int.natAbs_natCast, mul_one]

theorem shiftedChebyshev_leadingCoeff (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    (shiftedChebyshev K n).leadingCoeff = (2 : K) ^ (n - 1) * 2 ^ n := by
  have hdeg : (C 2 * X - 1 : K[X]).natDegree = 1 := by
    simpa only [← C_1, natDegree_sub_C] using natDegree_C_mul_X (R := K) 2 (by norm_num)
  have hlead : (C 2 * X - 1 : K[X]).leadingCoeff = 2 := by
    rw [leadingCoeff, hdeg]
    simp [coeff_one]
  rw [shiftedChebyshev, leadingCoeff_comp (by rw [hdeg]; decide), hlead,
    Chebyshev.leadingCoeff_T, Chebyshev.natDegree_T, Int.natAbs_natCast]

theorem shiftedChebyshev_ne_zero (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    shiftedChebyshev K n ≠ 0 := by
  rw [← leadingCoeff_ne_zero, shiftedChebyshev_leadingCoeff]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

theorem shiftedChebyshev_degree (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    (shiftedChebyshev K n).degree = n := by
  rw [degree_eq_natDegree (shiftedChebyshev_ne_zero K n), shiftedChebyshev_natDegree]

noncomputable def shiftedChebyshevSequence (K : Type*) [Field K] [CharZero K] : Sequence K where
  elems' := shiftedChebyshev K
  degree_eq' := shiftedChebyshev_degree K

theorem exists_shiftedChebyshev_expansion {K : Type*} [Field K] [CharZero K]
    (P : K[X]) (D : ℕ) (hP : P.degree < D) :
    ∃ c : Fin D → K, P = ∑ j, c j • shiftedChebyshev K j := by
  let S := shiftedChebyshevSequence K
  have hspan : Submodule.span K (Set.range (fun j : Fin D => shiftedChebyshev K j)) =
      degreeLT K D := by
    rw [← S.span_degreeLT (fun i _ => isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero i)))]
    congr 1
    ext Q
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.isLt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hmem : P ∈ Submodule.span K (Set.range (fun j : Fin D => shiftedChebyshev K j)) := by
    rw [hspan, mem_degreeLT]
    exact hP
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  exact ⟨c, hc.symm⟩

theorem shiftedChebyshev_eval (K : Type*) [Field K] (n : ℕ) (x : K) :
    (shiftedChebyshev K n).eval x = (Chebyshev.T K (n : ℤ)).eval (2 * x - 1) := by
  simp only [shiftedChebyshev, eval_comp, eval_sub, eval_mul, eval_C, eval_X, eval_one]

theorem shiftedChebyshev_real_abs_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |(shiftedChebyshev ℝ n).eval x| ≤ 1 := by
  rw [shiftedChebyshev_eval]
  exact Chebyshev.abs_eval_T_real_le_one n (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)

theorem shiftedChebyshev_real_derivative_abs_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |(shiftedChebyshev ℝ n).derivative.eval x| ≤ 2 * (n : ℝ) ^ 2 := by
  have harg : |2 * x - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := Chebyshev.abs_iterate_derivative_T_real_le (n : ℤ) 1 harg
  simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one, Int.cast_natCast] at h
  rw [shiftedChebyshev, derivative_comp]
  simp only [eval_mul, eval_comp, eval_sub, eval_C, eval_X, eval_one,
    derivative_sub, derivative_mul, derivative_C, zero_mul, derivative_X,
    mul_one, zero_add, derivative_one, sub_zero, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem shiftedChebyshev_real_difference_le (n : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |(shiftedChebyshev ℝ n).eval y - (shiftedChebyshev ℝ n).eval x| ≤
      2 * (n : ℝ) ^ 2 * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z => (shiftedChebyshev ℝ n).eval z)
    (fun z _ => (shiftedChebyshev ℝ n).differentiableAt)
    (fun z hz => by
      rw [Polynomial.deriv, Real.norm_eq_abs]
      exact shiftedChebyshev_real_derivative_abs_le n hz)
    (convex_Icc 0 1) hx hy
  simpa only [Real.norm_eq_abs] using h

theorem shiftedChebyshev_complex_eval (n : ℕ) (x : ℝ) :
    (shiftedChebyshev ℂ n).eval (x : ℂ) = Complex.ofReal ((shiftedChebyshev ℝ n).eval x) := by
  rw [shiftedChebyshev_eval, shiftedChebyshev_eval]
  norm_cast

theorem shiftedChebyshev_complex_norm_le (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    ‖(shiftedChebyshev ℂ n).eval (x : ℂ)‖ ≤ 1 := by
  rw [shiftedChebyshev_complex_eval, Complex.norm_real, Real.norm_eq_abs]
  exact shiftedChebyshev_real_abs_le n hx

end Erdos345
