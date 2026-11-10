import Erdos345.RegularizedCyclotomic

namespace Erdos345

open Finset Polynomial

theorem cyclotomicProduct_factor (S : Finset ℕ) (m : ℕ → ℕ) (t : ℕ) (ht : t ∈ S) :
    cyclotomicProduct S m = (cyclotomic t ℤ) ^ m t * cyclotomicProduct (S.erase t) m := by
  rw [mul_comm]
  exact (prod_erase_mul _ _ ht).symm

theorem eval_divByMonic_X_sub_C_eq_derivative {K : Type*} [Field K] (P : K[X]) (z : K) :
    (P /ₘ (X - C z)).eval z = P.derivative.eval z := by
  have h := congrArg (fun Q : K[X] => Q.eval z)
    (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative P z)
  simpa only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] using h

theorem complementFactor_of_factorization
    {K I : Type*} [Field K] [Fintype I] (z : I → K) (m : I → ℕ) (i : I)
    (U V F : K[X]) (hF : (X - C (z i)) * U = F)
    (hfactor : linearFactorProduct z m = F ^ m i * V) :
    complementFactor z m i = U ^ m i * V := by
  classical
  apply mul_left_cancel₀ (pow_ne_zero (m i) (X_sub_C_ne_zero (z i)))
  calc
    (X - C (z i)) ^ m i * complementFactor z m i = linearFactorProduct z m := by
      rw [mul_comm]
      exact prod_erase_mul _ _ (mem_univ i)
    _ = F ^ m i * V := hfactor
    _ = (X - C (z i)) ^ m i * (U ^ m i * V) := by rw [← hF, mul_pow, mul_assoc]

/-- The complement polynomial from the exponential expansion is exactly the
regularized cyclotomic denominator evaluated at its primitive root. -/
theorem complementFactor_eval_eq_regularized
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (i : CyclotomicRootIndex S) :
    (complementFactor (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m) i).eval
        (cyclotomicRootValue i) =
      regularizedCyclotomicValue S m i.1 (cyclotomicRootValue i) := by
  let z := cyclotomicRootValue i
  let F := cyclotomic (i.1 : ℕ) ℂ
  let U := F /ₘ (X - C z)
  let V := (cyclotomicProduct (S.erase i.1) m).map (Int.castRingHom ℂ)
  have hroot : F.IsRoot z :=
    (isRoot_cyclotomic_iff_charZero (hS i.1 i.1.property)).mpr
      (isPrimitiveRoot_of_mem_primitiveRoots i.2.property)
  have hlinear : (X - C z) * U = F := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hfactor : linearFactorProduct (@cyclotomicRootValue S) (cyclotomicRootMultiplicity m) =
      F ^ m i.1 * V := by
    rw [cyclotomicProduct_split S m hS, cyclotomicProduct_factor S m i.1 i.1.property,
      Polynomial.map_mul, Polynomial.map_pow, map_cyclotomic]
  have heq := complementFactor_of_factorization (@cyclotomicRootValue S)
    (cyclotomicRootMultiplicity m) i U V F hlinear hfactor
  rw [heq, eval_mul, eval_pow]
  change (F /ₘ (X - C z)).eval z ^ m i.1 * V.eval z = _
  rw [eval_divByMonic_X_sub_C_eq_derivative]
  simp only [regularizedCyclotomicValue, V, F, z, eval₂_eq_eval_map,
    ← derivative_map, map_cyclotomic]

end Erdos345
