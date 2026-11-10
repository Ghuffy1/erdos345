import Erdos345.RationalReductionPhase
import Erdos345.RoundedRecurrence

namespace Erdos345

open Finset Polynomial

theorem real_cast_flat_polynomial_annihilation (N : ℕ) (w : ℕ → ℕ) (P : ℚ[X])
    (hdeg : P.natDegree < weightMass N w) :
    shiftAction ((flatPolynomial N w).map (Int.castRingHom ℝ))
      (fun n : ℕ => ((P.eval (n : ℚ) : ℚ) : ℝ)) = 0 := by
  let φ : ℚ →+* ℝ := algebraMap ℚ ℝ
  have hmap : ((flatPolynomial N w).map (Int.castRingHom ℚ)).map φ =
      (flatPolynomial N w).map (Int.castRingHom ℝ) := by
    rw [Polynomial.map_map]
    congr 1
  have hrec := flatPolynomial_annihilates N w P hdeg
  funext n
  change shiftAction ((flatPolynomial N w).map (Int.castRingHom ℝ))
    (fun j : ℕ => φ (P.eval (j : ℚ))) n = 0
  rw [← hmap, shiftAction_map, congrFun hrec n]
  exact map_zero φ

/-- Rounding a reduced rational phase retains the original center energy
and produces an actual global integer recurrence on a quantified window. -/
theorem exists_reduced_phase_recurrence (N : ℕ) (w : ℕ → ℕ) (P : ℚ[X])
    (hdeg : P.natDegree < weightMass N w) (q u k X : ℕ) (hq : 0 < q)
    (hmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k)
    (hX : (flatPolynomial N w).natDegree ≤ X) :
    ∃ a L : ℕ, ∃ g : ℕ → ℤ,
      a + L ≤ X - (flatPolynomial N w).natDegree ∧
      ((X - (flatPolynomial N w).natDegree : ℕ) : ℝ) /
          (coefficientL1 (flatPolynomial N w) ^ 2 * centerEnergy k u q X / 4 + 1) - 1 ≤ (L : ℝ) ∧
      shiftAction (flatPolynomial N w) g = 0 ∧
      (∀ j < (flatPolynomial N w).natDegree + L,
        g (a + j) = round ((P.eval ((a + j : ℕ) : ℚ) : ℚ) : ℝ)) ∧
      (∑ j ∈ range ((flatPolynomial N w).natDegree + L),
        ‖((P.eval ((a + j : ℕ) : ℚ) - (g (a + j) : ℚ) : ℚ) : ℂ)‖ ^ 2)
        ≤ centerEnergy k u q X / 4 := by
  have hlead : (flatPolynomial N w).leadingCoeff ^ 2 = 1 := by
    rw [flatPolynomial_leadingCoeff, ← pow_mul, Nat.mul_comm (weightMass N w) 2, pow_mul]
    norm_num
  have hann := real_cast_flat_polynomial_annihilation N w P hdeg
  obtain ⟨a, L, g, ha, hL, hg, hmatch, henergy⟩ := exists_rounded_recurrence
    (flatPolynomial N w) (flatPolynomial_coeff_zero N w) hlead
    (fun n : ℕ => ((P.eval (n : ℚ) : ℚ) : ℝ))
    (X - (flatPolynomial N w).natDegree) X (by omega)
    (fun n _ => congrFun hann n)
  rw [rational_phase_sineEnergy_eq_center P q u k X hq hmod] at hL henergy
  refine ⟨a, L, g, ha, hL, hg, hmatch, ?_⟩
  convert henergy using 1
  apply sum_congr rfl
  intro j _
  rw [Complex.norm_ratCast, sq_abs, Rat.cast_sub, Rat.cast_intCast]

end Erdos345
