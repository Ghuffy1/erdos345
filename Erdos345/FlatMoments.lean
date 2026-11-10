import Erdos345.RoundedRecurrence

namespace Erdos345

open Finset Polynomial

theorem shiftAction_C {R : Type*} [CommRing R] (c : R) (f : ℕ → R) :
    shiftAction (C c) f = c • f := by
  funext n
  simp [shiftAction_sum]

theorem shiftAction_constant {R : Type*} [CommRing R] (p : R[X]) (c : R) (n : ℕ) :
    shiftAction p (fun _ => c) n = p.eval 1 * c := by
  rw [shiftAction_sum, eval_eq_sum_range]
  simp only [one_pow, mul_one, sum_mul]

theorem shiftAction_one_sub_X_power {R : Type*} [CommRing R] (f : ℕ → R) (s : ℕ) :
    shiftAction ((1 - X : R[X]) ^ s) f = (-1 : R) ^ s • iteratedDifference s f := by
  have heq : (1 - X : R[X]) ^ s = C ((-1 : R) ^ s) * (X - 1) ^ s := by
    have hlin : (1 - X : R[X]) = C (-1) * (X - 1) := by simp
    rw [hlin, mul_pow, map_pow]
  rw [heq, shiftAction_mul, shiftAction_C, shiftAction_difference_power]

theorem polynomial_top_difference_all (p : ℚ[X]) {s : ℕ}
    (hp : p.natDegree ≤ s) (n : ℕ) :
    iteratedDifference s (fun m : ℕ => p.eval (m : ℚ)) n =
      (s.factorial : ℚ) * p.coeff s := by
  let A := fun j => iteratedDifference j (fun m : ℕ => p.eval (m : ℚ)) 0
  have heq : (fun m : ℕ => p.eval (m : ℚ)) = newtonEval A := by
    funext m
    exact (newton_forward_formula (R := ℚ) (fun j : ℕ => p.eval (j : ℚ)) m).symm
  rw [heq, iteratedDifference_newtonEval]
  have hsum : newtonEval (fun j => A (j + s)) n = A s := by
    rw [newtonEval, sum_eq_single 0]
    · simp
    · intro j hj hj0
      have hjs : s < j + s := by omega
      have hz : A (j + s) = 0 := polynomial_difference_coefficient_zero p hp hjs
      rw [hz, zero_mul]
    · intro h
      exact False.elim (h (mem_range.mpr (Nat.succ_pos n)))
  rw [hsum]
  exact polynomial_top_difference p hp

/-- The first nonvanishing moment of the integer filter, as a constant
polynomial-action identity at every starting position. -/
theorem flatPolynomial_top_moment (N : ℕ) (a : ℕ → ℕ) (p : ℚ[X])
    (hp : p.natDegree ≤ weightMass N a) (n : ℕ) :
    shiftAction ((flatPolynomial N a).map (Int.castRingHom ℚ))
        (fun m : ℕ => p.eval (m : ℚ)) n =
      (-1 : ℚ) ^ weightMass N a * ((weightMass N a).factorial : ℚ) *
        (normalizedMoment N a : ℚ) * p.coeff (weightMass N a) := by
  have hfactor : (flatPolynomial N a).map (Int.castRingHom ℚ) =
      (flatQuotient N a).map (Int.castRingHom ℚ) * (1 - X) ^ weightMass N a := by
    rw [flatPolynomial_factor, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_one, map_X, mul_comm]
  rw [hfactor, shiftAction_mul, shiftAction_one_sub_X_power]
  have hdiff : iteratedDifference (weightMass N a) (fun m : ℕ => p.eval (m : ℚ)) =
      fun _ => ((weightMass N a).factorial : ℚ) * p.coeff (weightMass N a) := by
    funext m
    exact polynomial_top_difference_all p hp m
  rw [hdiff]
  change shiftAction ((flatQuotient N a).map (Int.castRingHom ℚ))
    (fun _ => (-1 : ℚ) ^ weightMass N a *
      (((weightMass N a).factorial : ℚ) * p.coeff (weightMass N a))) n = _
  rw [shiftAction_constant, eval_one_map, flatQuotient_eval_one]
  simp only [Int.coe_castRingHom, Int.cast_natCast]
  ring

theorem coefficientL1_flatQuotient (N : ℕ) (a : ℕ → ℕ) :
    coefficientL1 (flatQuotient N a) = (normalizedMoment N a : ℝ) := by
  have heval := eval_eq_sum_range (p := flatQuotient N a) (1 : ℤ)
  simp only [one_pow, mul_one] at heval
  calc
    coefficientL1 (flatQuotient N a) =
        ∑ i ∈ range ((flatQuotient N a).natDegree + 1), ((flatQuotient N a).coeff i : ℝ) := by
      apply sum_congr rfl
      intro i _
      apply abs_of_nonneg
      exact_mod_cast flatQuotient_coeff_nonneg N a i
    _ = (((flatQuotient N a).eval (1 : ℤ) : ℤ) : ℝ) := by exact_mod_cast heval.symm
    _ = (normalizedMoment N a : ℝ) := by rw [flatQuotient_eval_one]; rfl

theorem coefficientL1_flatPolynomial_ge_one (N : ℕ) (a : ℕ → ℕ) :
    1 ≤ coefficientL1 (flatPolynomial N a) := by
  have h := single_le_sum
    (f := fun i => |((flatPolynomial N a).coeff i : ℝ)|)
    (s := range ((flatPolynomial N a).natDegree + 1))
    (fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.succ_pos _))
  simpa only [coefficientL1, flatPolynomial_coeff_zero, Int.cast_one, abs_one] using h

end Erdos345
