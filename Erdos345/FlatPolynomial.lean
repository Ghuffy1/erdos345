import Erdos345.MonotoneLayers
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

namespace Erdos345

open Finset Polynomial

noncomputable def geometricNat (n : ℕ) : ℕ[X] := ∑ j ∈ range n, X ^ j

noncomputable def flatQuotientNat (N : ℕ) (a : ℕ → ℕ) : ℕ[X] :=
  ∏ i ∈ range N, geometricNat (i + 1) ^ a i

noncomputable def flatQuotient (N : ℕ) (a : ℕ → ℕ) : ℤ[X] :=
  (flatQuotientNat N a).map (Nat.castRingHom ℤ)

noncomputable def flatPolynomial (N : ℕ) (a : ℕ → ℕ) : ℤ[X] :=
  ∏ i ∈ range N, (1 - X ^ (i + 1)) ^ a i

theorem geometricNat_map (n : ℕ) :
    (geometricNat n).map (Nat.castRingHom ℤ) = ∑ j ∈ range n, (X : ℤ[X]) ^ j := by
  simp [geometricNat, Polynomial.map_sum]

theorem flatQuotient_eq_product (N : ℕ) (a : ℕ → ℕ) :
    flatQuotient N a = ∏ i ∈ range N, (∑ j ∈ range (i + 1), (X : ℤ[X]) ^ j) ^ a i := by
  simp [flatQuotient, flatQuotientNat, Polynomial.map_prod, geometricNat_map]

theorem flatQuotient_coeff_nonneg (N : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    0 ≤ (flatQuotient N a).coeff j := by
  simp only [flatQuotient, coeff_map]
  exact Nat.cast_nonneg _

theorem flatQuotient_eval_one (N : ℕ) (a : ℕ → ℕ) :
    (flatQuotient N a).eval 1 = (normalizedMoment N a : ℤ) := by
  rw [flatQuotient_eq_product]
  simp [normalizedMoment, eval_prod, eval_finsetSum]

theorem flatQuotient_eval_one_pos (N : ℕ) (a : ℕ → ℕ) :
    0 < (flatQuotient N a).eval 1 := by
  rw [flatQuotient_eval_one]
  exact_mod_cast normalizedMoment_pos N a

theorem flatQuotient_eval_one_dvd {N : ℕ} {a : ℕ → ℕ}
    (ha : AntitoneOn a (Set.Iio N)) :
    (flatQuotient N a).eval 1 ∣ ((weightMass N a).factorial : ℤ) := by
  rw [flatQuotient_eval_one]
  exact_mod_cast normalizedMoment_dvd_factorial ha

theorem flatPolynomial_factor (N : ℕ) (a : ℕ → ℕ) :
    flatPolynomial N a = (1 - X) ^ weightMass N a * flatQuotient N a := by
  rw [flatPolynomial, flatQuotient_eq_product]
  calc
    (∏ i ∈ range N, (1 - (X : ℤ[X]) ^ (i + 1)) ^ a i) =
        ∏ i ∈ range N, ((1 - X) * ∑ j ∈ range (i + 1), X ^ j) ^ a i := by
      apply prod_congr rfl
      intro i _
      rw [mul_neg_geom_sum]
    _ = (∏ i ∈ range N, (1 - X) ^ a i) *
        ∏ i ∈ range N, (∑ j ∈ range (i + 1), X ^ j) ^ a i := by
      simp only [mul_pow, prod_mul_distrib]
    _ = _ := by rw [prod_pow_eq_pow_sum]; rfl

theorem flatPolynomial_coeff_zero (N : ℕ) (a : ℕ → ℕ) :
    (flatPolynomial N a).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  simp [flatPolynomial, eval_prod]

theorem flatPolynomial_ne_zero (N : ℕ) (a : ℕ → ℕ) : flatPolynomial N a ≠ 0 := by
  intro h
  have hc := flatPolynomial_coeff_zero N a
  rw [h, coeff_zero] at hc
  exact zero_ne_one hc

theorem one_sub_X_pow_natDegree (i : ℕ) :
    (1 - (X : ℤ[X]) ^ (i + 1)).natDegree = i + 1 := by
  have heq : (1 - (X : ℤ[X]) ^ (i + 1)) = -(X ^ (i + 1) - C 1) := by simp
  rw [heq, natDegree_neg, natDegree_X_pow_sub_C]

theorem one_sub_X_pow_leadingCoeff (i : ℕ) :
    (1 - (X : ℤ[X]) ^ (i + 1)).leadingCoeff = -1 := by
  have heq : (1 - (X : ℤ[X]) ^ (i + 1)) = -(X ^ (i + 1) - C 1) := by simp
  rw [heq, leadingCoeff_neg, leadingCoeff_X_pow_sub_C (by omega)]

theorem flatPolynomial_leadingCoeff (N : ℕ) (a : ℕ → ℕ) :
    (flatPolynomial N a).leadingCoeff = (-1 : ℤ) ^ weightMass N a := by
  simp only [flatPolynomial, leadingCoeff_prod, leadingCoeff_pow,
    one_sub_X_pow_leadingCoeff, prod_pow_eq_pow_sum, weightMass]

theorem flatPolynomial_natDegree (N : ℕ) (a : ℕ → ℕ) :
    (flatPolynomial N a).natDegree = ∑ i ∈ range N, (i + 1) * a i := by
  rw [flatPolynomial, natDegree_prod]
  · apply sum_congr rfl
    intro i _
    rw [natDegree_pow, one_sub_X_pow_natDegree, Nat.mul_comm]
  · intro i _
    apply pow_ne_zero
    intro h
    have hc : (1 - (X : ℤ[X]) ^ (i + 1)).coeff 0 = 1 := by simp
    rw [h, coeff_zero] at hc
    exact zero_ne_one hc

theorem flatPolynomial_natDegree_le (N : ℕ) (a : ℕ → ℕ) :
    (flatPolynomial N a).natDegree ≤ N * weightMass N a := by
  rw [flatPolynomial_natDegree, weightMass, mul_sum]
  apply sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_right (a i) (mem_range.mp hi)

theorem one_sub_X_power_dvd_flatPolynomial (N : ℕ) (a : ℕ → ℕ) :
    ((1 - X : ℤ[X]) ^ weightMass N a) ∣ flatPolynomial N a :=
  ⟨flatQuotient N a, flatPolynomial_factor N a⟩

theorem flatPolynomial_rootMultiplicity_one (N : ℕ) (a : ℕ → ℕ) :
    (flatPolynomial N a).rootMultiplicity 1 = weightMass N a := by
  let R : ℤ[X] := (C (-1)) ^ weightMass N a * flatQuotient N a
  have hRval : R.eval 1 ≠ 0 := by
    dsimp only [R]
    rw [eval_mul, eval_pow, eval_C]
    exact mul_ne_zero (pow_ne_zero _ (by decide)) (ne_of_gt (flatQuotient_eval_one_pos N a))
  have hR : R ≠ 0 := by
    intro h
    exact hRval (by rw [h, eval_zero])
  have hroot : R.rootMultiplicity 1 = 0 :=
    rootMultiplicity_eq_zero hRval
  have hlin : (1 - X : ℤ[X]) = C (-1) * (X - C 1) := by simp
  have heq : flatPolynomial N a = R * (X - C 1) ^ weightMass N a := by
    rw [flatPolynomial_factor, hlin, mul_pow]
    dsimp only [R]
    ring
  rw [heq, rootMultiplicity_mul_X_sub_C_pow hR, hroot, zero_add]

end Erdos345
