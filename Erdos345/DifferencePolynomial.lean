import Erdos345.QuasipolynomialPrefixGrowth

namespace Erdos345

open Finset Polynomial

/-- A global integral sequence with vanishing (k+1)-st difference is the
restriction of an integer-valued rational polynomial. Its top numerator
is the actual kth forward difference at zero. -/
theorem polynomial_of_vanishing_difference (f : ℕ → ℤ) (k : ℕ)
    (hf : iteratedDifference (k + 1) f = 0) :
    ∃ P : ℚ[X], ∃ u : ℤ, P.natDegree ≤ k ∧ integerValuedPolynomial P ∧
      (∀ n : ℕ, P.eval (n : ℚ) = (f n : ℚ)) ∧ P.coeff k = (u : ℚ) / k.factorial := by
  let A : ℕ → ℤ := fun j => iteratedDifference j f 0
  have htail : ∀ j : ℕ, k < j → A j = 0 := by
    intro j hj
    have heq : j = (k + 1) + (j - (k + 1)) := by omega
    dsimp only [A]
    rw [heq, iteratedDifference_add, hf]
    exact iteratedDifference_zero_of_prefix 0 _ _ (fun i _ => rfl)
  have htr : truncateCoefficients A k = A := by
    funext j
    by_cases hj : j ≤ k
    · simp only [truncateCoefficients, ite_eq_left hj]
    · simp only [truncateCoefficients, ite_eq_right hj, htail j (by omega)]
  refine ⟨newtonPolynomial (fun j => (A j : ℚ)) k, A k,
    newtonPolynomial_natDegree_le _ _, newtonPolynomial_integerValued A k, ?_, ?_⟩
  · intro n
    rw [newtonPolynomial_eval_nat]
    have h := newton_forward_formula f n
    change newtonEval A n = f n at h
    rw [← htr, newtonEval_truncate_eq_sum] at h
    exact_mod_cast h
  · rw [newtonPolynomial_coeff_top]
    rfl

theorem flat_quotient_vanishing_difference (N : ℕ) (w : ℕ → ℕ) (g : ℕ → ℤ)
    (hg : shiftAction (flatPolynomial N w) g = 0) :
    iteratedDifference (weightMass N w) (shiftAction (flatQuotient N w) g) = 0 := by
  rw [flatPolynomial_factor, shiftAction_mul, shiftAction_one_sub_X_power] at hg
  funext n
  have h := congrFun hg n
  change (-1 : ℤ) ^ weightMass N w *
    iteratedDifference (weightMass N w) (shiftAction (flatQuotient N w) g) n = 0 at h
  change iteratedDifference (weightMass N w) (shiftAction (flatQuotient N w) g) n = 0
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by decide))

theorem exists_flat_quotient_polynomial (N : ℕ) (w : ℕ → ℕ) (g : ℕ → ℤ) (k : ℕ)
    (hmass : weightMass N w = k + 1) (hg : shiftAction (flatPolynomial N w) g = 0) :
    ∃ P : ℚ[X], ∃ u : ℤ, P.natDegree ≤ k ∧ integerValuedPolynomial P ∧
      (∀ n : ℕ, P.eval (n : ℚ) = (shiftAction (flatQuotient N w) g n : ℚ)) ∧
      P.coeff k = (u : ℚ) / k.factorial := by
  have h := flat_quotient_vanishing_difference N w g hg
  rw [hmass] at h
  exact polynomial_of_vanishing_difference _ k h

end Erdos345
