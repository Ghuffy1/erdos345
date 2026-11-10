import Erdos345.DifferencePolynomial
import Mathlib.Algebra.Polynomial.Taylor

namespace Erdos345

open Finset Polynomial

noncomputable def polynomialShiftAction {R : Type*} [CommRing R] (Q P : R[X]) : R[X] :=
  ∑ i ∈ range (Q.natDegree + 1), C (Q.coeff i) * taylor (i : R) P

theorem polynomialShiftAction_eval {R : Type*} [CommRing R] (Q P : R[X]) (n : ℕ) :
    (polynomialShiftAction Q P).eval (n : R) =
      shiftAction Q (fun j : ℕ => P.eval (j : R)) n := by
  rw [polynomialShiftAction, eval_finsetSum, shiftAction_sum]
  apply sum_congr rfl
  intro i _
  simp only [eval_mul, eval_C, taylor_apply, eval_comp, eval_add, eval_X, Nat.cast_add]

theorem polynomialShiftAction_degree {R : Type*} [CommRing R]
    (Q P : R[X]) (k : ℕ) (hP : P.natDegree ≤ k) :
    (polynomialShiftAction Q P).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le _ _).trans (by simpa only [natDegree_taylor] using hP)

theorem taylor_coeff_of_natDegree_le {R : Type*} [CommRing R] (P : R[X]) (a : R)
    (k : ℕ) (hP : P.natDegree ≤ k) : (taylor a P).coeff k = P.coeff k := by
  by_cases h : P.natDegree = k
  · have hc := coeff_taylor_natDegree (r := a) (f := P)
    rw [h, leadingCoeff, h] at hc
    exact hc
  · have hlt : P.natDegree < k := by omega
    have ht : (taylor a P).natDegree < k := by simpa only [natDegree_taylor] using hlt
    rw [coeff_eq_zero_of_natDegree_lt ht, coeff_eq_zero_of_natDegree_lt hlt]

theorem polynomialShiftAction_top {R : Type*} [CommRing R]
    (Q P : R[X]) (k : ℕ) (hP : P.natDegree ≤ k) :
    (polynomialShiftAction Q P).coeff k = Q.eval 1 * P.coeff k := by
  rw [polynomialShiftAction, finsetSum_coeff]
  simp only [coeff_C_mul, taylor_coeff_of_natDegree_le P _ k hP]
  rw [← sum_mul, eval_eq_sum_range]
  simp only [one_pow, mul_one]

end Erdos345
