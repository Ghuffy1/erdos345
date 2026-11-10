import Erdos345.PolynomialSampleEnergy

namespace Erdos345

open Finset Polynomial

theorem exists_inverse_error_polynomial (N : ℕ) (w : ℕ → ℕ) (g : ℕ → ℤ)
    (k : ℕ) (hmass : weightMass N w = k + 1)
    (hg : shiftAction (flatPolynomial N w) g = 0) (α : ℝ) :
    ∃ u : ℤ, ∃ P : ℝ[X], P.natDegree ≤ k ∧
      P.coeff k = (normalizedMoment N w : ℝ) *
        (α - (u : ℝ) / ((k.factorial * normalizedMoment N w : ℕ) : ℝ)) ∧
      ∀ n : ℕ, P.eval (n : ℝ) =
        shiftAction ((flatQuotient N w).map (Int.castRingHom ℝ))
          (fun j : ℕ => α * (j : ℝ) ^ k - (g j : ℝ)) n := by
  obtain ⟨B, u, hB, _hInt, hBeval, hBtop⟩ := exists_flat_quotient_polynomial N w g k hmass hg
  let Q := (flatQuotient N w).map (Int.castRingHom ℝ)
  let F : ℝ[X] := C α * X ^ k
  let P := polynomialShiftAction Q F - B.map (algebraMap ℚ ℝ)
  have hF : F.natDegree ≤ k := by
    exact (natDegree_C_mul_le α (X ^ k)).trans (by simp)
  have hP : P.natDegree ≤ k := (natDegree_sub_le _ _).trans
    (max_le (polynomialShiftAction_degree Q F k hF) (natDegree_map_le.trans hB))
  have hQeval : Q.eval 1 = (normalizedMoment N w : ℝ) := by
    dsimp only [Q]
    rw [eval_one_map, flatQuotient_eval_one]
    simp only [Int.coe_castRingHom, Int.cast_natCast]
  have hBtopR : (B.map (algebraMap ℚ ℝ)).coeff k = (u : ℝ) / (k.factorial : ℝ) := by
    rw [coeff_map, hBtop]
    simp only [map_div₀, map_intCast, map_natCast]
  have hBevalR (n : ℕ) : (B.map (algebraMap ℚ ℝ)).eval (n : ℝ) =
      (shiftAction (flatQuotient N w) g n : ℝ) := by
    have h := congrArg (algebraMap ℚ ℝ) (hBeval n)
    have he := eval_map_apply (f := algebraMap ℚ ℝ) (p := B) (n : ℚ)
    rw [map_natCast] at he
    exact he.trans (by simpa only [map_intCast] using h)
  refine ⟨u, P, hP, ?_, ?_⟩
  · dsimp only [P]
    rw [coeff_sub, polynomialShiftAction_top Q F k hF, hQeval, hBtopR]
    have hFtop : F.coeff k = α := by simp [F]
    rw [hFtop]
    have hM : (normalizedMoment N w : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (normalizedMoment_pos N w)
    have hkfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    push_cast
    field_simp
  · intro n
    dsimp only [P]
    rw [eval_sub, polynomialShiftAction_eval, hBevalR]
    have hQg := shiftAction_map (Int.castRingHom ℝ) (flatQuotient N w) g n
    change shiftAction Q (fun j : ℕ => (g j : ℝ)) n =
      (shiftAction (flatQuotient N w) g n : ℝ) at hQg
    rw [← hQg]
    have heq : (fun j : ℕ => F.eval (j : ℝ)) = (fun j : ℕ => α * (j : ℝ) ^ k) := by
      funext j
      simp only [F, eval_mul, eval_C, eval_pow, eval_X]
    rw [heq]
    exact (congrFun (map_sub (shiftAction Q) (fun j : ℕ => α * (j : ℝ) ^ k) (fun j : ℕ => (g j : ℝ))) n).symm

theorem flatQuotient_natDegree_le (N : ℕ) (w : ℕ → ℕ) :
    (flatQuotient N w).natDegree ≤ (flatPolynomial N w).natDegree := by
  have hdiv : flatQuotient N w ∣ flatPolynomial N w := by
    refine ⟨(1 - X) ^ weightMass N w, ?_⟩
    rw [mul_comm]
    exact flatPolynomial_factor N w
  exact natDegree_le_of_dvd hdiv (flatPolynomial_ne_zero N w)

end Erdos345
