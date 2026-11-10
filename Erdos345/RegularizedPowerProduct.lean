import Erdos345.RegularizedComplement
import Mathlib.Analysis.Normed.Ring.Finite

namespace Erdos345

open Finset Polynomial

noncomputable def regularizedPowerFactor (t h : ℕ) (z : ℂ) : ℂ[X] :=
  if t ∣ h then (X ^ h - 1) /ₘ (X - C z) else X ^ h - 1

noncomputable def regularizedPowerProduct (N : ℕ) (w : ℕ → ℕ) (t : ℕ) (z : ℂ) : ℂ[X] :=
  ∏ i ∈ range N, regularizedPowerFactor t (i + 1) z ^ w i

noncomputable def rawFlatPolynomial (N : ℕ) (w : ℕ → ℕ) : ℤ[X] :=
  ∏ i ∈ range N, (X ^ (i + 1) - 1) ^ w i

theorem rawFlatPolynomial_eq_cyclotomic (N : ℕ) (w : ℕ → ℕ) :
    rawFlatPolynomial N w = cyclotomicProduct (Icc 1 N) (rootSlots N w) := by
  rw [← flatPolynomial_cyclotomic_factorization]
  symm
  calc
    (-1 : ℤ[X]) ^ weightMass N w * flatPolynomial N w =
        ∏ i ∈ range N, (-1 : ℤ[X]) ^ w i * (1 - X ^ (i + 1)) ^ w i := by
      rw [weightMass, ← prod_pow_eq_pow_sum, flatPolynomial, prod_mul_distrib]
    _ = rawFlatPolynomial N w := by
      apply prod_congr rfl
      intro i _
      rw [← mul_pow]
      congr 1
      ring

theorem regularizedPowerFactor_factor
    (t h a : ℕ) (z : ℂ) (hz : IsPrimitiveRoot z t) :
    (X - C z) ^ (if t ∣ h then a else 0) * regularizedPowerFactor t h z ^ a =
      ((X : ℂ[X]) ^ h - 1) ^ a := by
  by_cases hd : t ∣ h
  · have hzh : z ^ h = 1 := by
      obtain ⟨v, rfl⟩ := hd
      rw [pow_mul, hz.pow_eq_one, one_pow]
    have hroot : ((X : ℂ[X]) ^ h - 1).IsRoot z := by
      simp only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_one, hzh, sub_self]
    have heq := mul_divByMonic_eq_iff_isRoot.mpr hroot
    rw [regularizedPowerFactor, ite_eq_left hd, ite_eq_left hd, ← mul_pow, heq]
  · simp only [regularizedPowerFactor, ite_eq_right hd, pow_zero, one_mul]

theorem regularizedPowerProduct_factor
    (N : ℕ) (w : ℕ → ℕ) (t : ℕ) (z : ℂ) (hz : IsPrimitiveRoot z t) :
    (X - C z) ^ rootSlots N w t * regularizedPowerProduct N w t z =
      (rawFlatPolynomial N w).map (Int.castRingHom ℂ) := by
  rw [regularizedPowerProduct, rootSlots, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  simp only [rawFlatPolynomial, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_sub, map_X, Polynomial.map_one]
  apply prod_congr rfl
  intro i _
  exact regularizedPowerFactor_factor t (i + 1) (w i) z hz

theorem regularizedPowerFactor_norm_of_dvd
    (t h : ℕ) (ht : 0 < t) (z : ℂ) (hz : IsPrimitiveRoot z t) (hd : t ∣ h) :
    ‖(regularizedPowerFactor t h z).eval z‖ = (h : ℝ) := by
  have hnorm : ‖z‖ = 1 := (hz.isOfFinOrder (Nat.ne_of_gt ht)).norm_eq_one
  rw [regularizedPowerFactor, ite_eq_left hd, eval_divByMonic_X_sub_C_eq_derivative]
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul,
    eval_C, eval_pow, eval_X, norm_mul, Complex.norm_natCast, norm_pow, hnorm,
    one_pow, mul_one]

theorem regularizedPowerFactor_primitive_norm_product
    (p k h : ℕ) (hp : p.Prime) (hh : 0 < h) :
    (∏ z ∈ primitiveRoots (p ^ (k + 1)) ℂ, ‖(regularizedPowerFactor (p ^ (k + 1)) h z).eval z‖) =
      if p ^ (k + 1) ∣ h then (h : ℝ) ^ (p ^ (k + 1)).totient
      else (p : ℝ) ^ (p ^ h.factorization p) := by
  by_cases hd : p ^ (k + 1) ∣ h
  · rw [ite_eq_left hd]
    have hn := pow_pos hp.pos (k + 1)
    have hcard : (primitiveRoots (p ^ (k + 1)) ℂ).card = (p ^ (k + 1)).totient :=
      (Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hn)).card_primitiveRoots
    calc
      _ = ∏ _z ∈ primitiveRoots (p ^ (k + 1)) ℂ, (h : ℝ) := by
        apply prod_congr rfl
        intro z hz
        exact regularizedPowerFactor_norm_of_dvd _ _ hn z
          (isPrimitiveRoot_of_mem_primitiveRoots hz) hd
      _ = _ := by rw [prod_const, hcard]
  · rw [ite_eq_right hd]
    simp only [regularizedPowerFactor, ite_eq_right hd, eval_sub, eval_pow, eval_X, eval_one]
    exact primePower_general_power_norm_product p k h hp hh hd

end Erdos345
