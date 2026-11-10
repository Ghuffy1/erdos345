import Erdos345.PrimePowerSlotBound

namespace Erdos345

open Finset Polynomial

theorem cyclotomicProduct_add (S : Finset ℕ) (a b : ℕ → ℕ) :
    cyclotomicProduct S (fun n => a n + b n) = cyclotomicProduct S a * cyclotomicProduct S b := by
  simp only [cyclotomicProduct, pow_add, prod_mul_distrib]

theorem cyclotomicProduct_congr (S : Finset ℕ) (a b : ℕ → ℕ)
    (hab : ∀ n ∈ S, a n = b n) : cyclotomicProduct S a = cyclotomicProduct S b := by
  apply prod_congr rfl
  intro n hn
  rw [hab n hn]

noncomputable def regularizedCyclotomicValue (S : Finset ℕ) (m : ℕ → ℕ) (t : ℕ) (z : ℂ) : ℂ :=
  ((cyclotomic t ℤ).derivative.eval₂ (Int.castRingHom ℂ) z) ^ m t *
    (cyclotomicProduct (S.erase t) m).eval₂ (Int.castRingHom ℂ) z

noncomputable def regularizedCyclotomicNorm (S : Finset ℕ) (m : ℕ → ℕ) (t : ℕ) : ℝ :=
  ∏ z ∈ primitiveRoots t ℂ, ‖regularizedCyclotomicValue S m t z‖

theorem cyclotomic_derivative_eval_ne_zero (t : ℕ) (ht : 0 < t) (z : ℂ)
    (hz : z ∈ primitiveRoots t ℂ) :
    (cyclotomic t ℤ).derivative.eval₂ (Int.castRingHom ℂ) z ≠ 0 := by
  let : NeZero (t : ℂ) := ⟨Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht)⟩
  have hr : (cyclotomic t ℂ).IsRoot z :=
    (isRoot_cyclotomic_iff_charZero ht).mpr (isPrimitiveRoot_of_mem_primitiveRoots hz)
  have hd := (separable_cyclotomic t ℂ).eval₂_derivative_ne_zero (RingHom.id ℂ)
    (by simpa only [eval₂_id, Polynomial.IsRoot] using hr)
  rw [eval₂_eq_eval_map, ← derivative_map, map_cyclotomic]
  simpa only [eval₂_id] using hd

theorem cyclotomicComplement_eval_ne_zero
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n)
    (t : ℕ) (z : ℂ) (hz : z ∈ primitiveRoots t ℂ) :
    (cyclotomicProduct (S.erase t) m).eval₂ (Int.castRingHom ℂ) z ≠ 0 := by
  simp only [eval₂_eq_eval_map, cyclotomicProduct, Polynomial.map_prod, Polynomial.map_pow,
    map_cyclotomic, eval_prod, eval_pow]
  apply prod_ne_zero_iff.mpr
  intro n hn
  apply pow_ne_zero
  intro heq
  have hnr : IsPrimitiveRoot z n :=
    (isRoot_cyclotomic_iff_charZero (hS n (mem_of_mem_erase hn))).mp heq
  have htr := isPrimitiveRoot_of_mem_primitiveRoots hz
  exact (mem_erase.mp hn).1 (hnr.unique htr)

theorem regularizedCyclotomicValue_ne_zero
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n)
    (t : ℕ) (ht : 0 < t) (z : ℂ) (hz : z ∈ primitiveRoots t ℂ) :
    regularizedCyclotomicValue S m t z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (cyclotomic_derivative_eval_ne_zero t ht z hz))
    (cyclotomicComplement_eval_ne_zero S m hS t z hz)

/-- Regularized denominator products have a nonzero integer resultant, even
when the individual values are not integers or do not have modulus at least one. -/
theorem regularizedCyclotomicNorm_ge_one
    (S : Finset ℕ) (m : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (t : ℕ) (ht : 0 < t) :
    1 ≤ regularizedCyclotomicNorm S m t := by
  let A : ℤ[X] := (cyclotomic t ℤ).derivative ^ m t * cyclotomicProduct (S.erase t) m
  have hn : ∀ z ∈ primitiveRoots t ℂ, A.eval₂ (Int.castRingHom ℂ) z ≠ 0 := by
    intro z hz
    simpa only [A, eval₂_mul, eval₂_pow, regularizedCyclotomicValue] using
      regularizedCyclotomicValue_ne_zero S m hS t ht z hz
  simpa only [A, eval₂_mul, eval₂_pow, regularizedCyclotomicValue, regularizedCyclotomicNorm] using
    primitive_value_norm_product_ge_one t ht A hn

theorem regularizedCyclotomicValue_add (S : Finset ℕ) (a b : ℕ → ℕ) (t : ℕ) (z : ℂ) :
    regularizedCyclotomicValue S (fun n => a n + b n) t z =
      regularizedCyclotomicValue S a t z * regularizedCyclotomicValue S b t z := by
  rw [regularizedCyclotomicValue, cyclotomicProduct_add, eval₂_mul, pow_add]
  unfold regularizedCyclotomicValue
  ring

theorem regularizedCyclotomicNorm_add (S : Finset ℕ) (a b : ℕ → ℕ) (t : ℕ) :
    regularizedCyclotomicNorm S (fun n => a n + b n) t =
      regularizedCyclotomicNorm S a t * regularizedCyclotomicNorm S b t := by
  simp only [regularizedCyclotomicNorm, regularizedCyclotomicValue_add, norm_mul, prod_mul_distrib]

theorem regularizedCyclotomicValue_congr
    (S : Finset ℕ) (a b : ℕ → ℕ) (t : ℕ) (ht : t ∈ S) (z : ℂ)
    (hab : ∀ n ∈ S, a n = b n) :
    regularizedCyclotomicValue S a t z = regularizedCyclotomicValue S b t z := by
  rw [regularizedCyclotomicValue, regularizedCyclotomicValue, hab t ht,
    cyclotomicProduct_congr (S.erase t) a b (fun n hn => hab n (mem_of_mem_erase hn))]

/-- Cancelling a collection of whole cyclotomic factors cannot increase the
product of regularized denominator norms over the primitive conjugates. -/
theorem regularizedCyclotomicNorm_mono
    (S : Finset ℕ) (a b : ℕ → ℕ) (hS : ∀ n ∈ S, 0 < n) (t : ℕ) (ht : t ∈ S)
    (hab : ∀ n ∈ S, a n ≤ b n) :
    regularizedCyclotomicNorm S a t ≤ regularizedCyclotomicNorm S b t := by
  let d : ℕ → ℕ := fun n => b n - a n
  have heq : regularizedCyclotomicNorm S b t = regularizedCyclotomicNorm S a t *
      regularizedCyclotomicNorm S d t := by
    rw [← regularizedCyclotomicNorm_add]
    apply prod_congr rfl
    intro z _
    congr 1
    exact regularizedCyclotomicValue_congr S b (fun n => a n + d n) t ht z
      (fun n hn => (Nat.add_sub_of_le (hab n hn)).symm)
  have hd := regularizedCyclotomicNorm_ge_one S d hS t (hS t ht)
  have ha : 0 ≤ regularizedCyclotomicNorm S a t := prod_nonneg (fun _ _ => norm_nonneg _)
  rw [heq]
  nlinarith

end Erdos345
