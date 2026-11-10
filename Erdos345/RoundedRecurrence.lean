import Erdos345.RecurrenceExtension
import Erdos345.RoundingEnergy

namespace Erdos345

open Finset Polynomial

theorem rounded_residual_count_bound (p : ℤ[X]) (f : ℕ → ℝ)
    (T X : ℕ) (hTX : T + p.natDegree ≤ X)
    (han : ∀ n < T, shiftAction (p.map (Int.castRingHom ℝ)) f n = 0) :
    (((range T).filter (fun n => shiftAction p (fun j => round (f j)) n ≠ 0)).card : ℝ) ≤
      coefficientL1 p ^ 2 * sineEnergy f X / 4 := by
  have hcount := recurrence_residual_count_bound p f (fun j => round (f j)) T X hTX han
  have hsum := mul_le_mul_of_nonneg_left (rounding_error_energy_le f X)
    (sq_nonneg (coefficientL1 p))
  calc
    _ ≤ coefficientL1 p ^ 2 * ∑ n ∈ range X, (f n - (round (f n) : ℝ)) ^ 2 := hcount
    _ ≤ coefficientL1 p ^ 2 * (sineEnergy f X / 4) := hsum
    _ = _ := by ring

/-- A global integer recurrence agrees with the rounded real sequence on a
quantified interval, with the original sampled error bound retained there. -/
theorem exists_rounded_recurrence (p : ℤ[X]) (hp0 : p.coeff 0 = 1)
    (hpD : p.leadingCoeff ^ 2 = 1) (f : ℕ → ℝ)
    (T X : ℕ) (hTX : T + p.natDegree ≤ X)
    (han : ∀ n < T, shiftAction (p.map (Int.castRingHom ℝ)) f n = 0) :
    ∃ a L : ℕ, ∃ g : ℕ → ℤ,
      a + L ≤ T ∧
      (T : ℝ) / (coefficientL1 p ^ 2 * sineEnergy f X / 4 + 1) - 1 ≤ (L : ℝ) ∧
      shiftAction p g = 0 ∧
      (∀ j < p.natDegree + L, g (a + j) = round (f (a + j))) ∧
      (∑ j ∈ range (p.natDegree + L), (f (a + j) - (g (a + j) : ℝ)) ^ 2)
        ≤ sineEnergy f X / 4 := by
  obtain ⟨a, L, ha, hL, hz⟩ := exists_zero_run_of_badcount
    (fun n => shiftAction p (fun j => round (f j)) n) T
    (coefficientL1 p ^ 2 * sineEnergy f X / 4)
    (rounded_residual_count_bound p f T X hTX han)
  obtain ⟨g, hg, hmatch⟩ := exists_integral_recurrence_extension p hp0 hpD
    (fun j => round (f j)) a L hz
  refine ⟨a, L, g, ha, hL, hg, hmatch, ?_⟩
  calc
    (∑ j ∈ range (p.natDegree + L), (f (a + j) - (g (a + j) : ℝ)) ^ 2) =
        ∑ j ∈ range (p.natDegree + L), (f (a + j) - (round (f (a + j)) : ℝ)) ^ 2 := by
      apply sum_congr rfl
      intro j hj
      rw [hmatch j (mem_range.mp hj)]
    _ ≤ ∑ n ∈ range X, (f n - (round (f n) : ℝ)) ^ 2 := by
      have hshift := shifted_nonnegative_sum_le
        (fun n => (f n - (round (f n) : ℝ)) ^ 2) (fun n => sq_nonneg _)
        (show p.natDegree + L + a ≤ X by omega)
      simpa only [Nat.add_comm] using hshift
    _ ≤ sineEnergy f X / 4 := rounding_error_energy_le f X

theorem exists_flat_power_recurrence (N : ℕ) (a : ℕ → ℕ) (k : ℕ)
    (hk : k < weightMass N a) (α : ℝ) (X : ℕ)
    (hX : (flatPolynomial N a).natDegree ≤ X) :
    ∃ b L : ℕ, ∃ g : ℕ → ℤ,
      b + L ≤ X - (flatPolynomial N a).natDegree ∧
      ((X - (flatPolynomial N a).natDegree : ℕ) : ℝ) /
          (coefficientL1 (flatPolynomial N a) ^ 2 * sineEnergy (fun n => α * (n : ℝ) ^ k) X / 4 + 1)
        - 1 ≤ (L : ℝ) ∧
      shiftAction (flatPolynomial N a) g = 0 ∧
      (∀ j < (flatPolynomial N a).natDegree + L,
        g (b + j) = round (α * ((b + j : ℕ) : ℝ) ^ k)) ∧
      (∑ j ∈ range ((flatPolynomial N a).natDegree + L),
        (α * ((b + j : ℕ) : ℝ) ^ k - (g (b + j) : ℝ)) ^ 2)
        ≤ sineEnergy (fun n => α * (n : ℝ) ^ k) X / 4 := by
  apply exists_rounded_recurrence (flatPolynomial N a) (flatPolynomial_coeff_zero N a) _
    (fun n => α * (n : ℝ) ^ k) (X - (flatPolynomial N a).natDegree) X
    (by omega)
  · intro n _
    exact congrFun (flatPolynomial_annihilates_power N a k hk α) n
  · rw [flatPolynomial_leadingCoeff, ← pow_mul, Nat.mul_comm (weightMass N a) 2, pow_mul]
    norm_num

end Erdos345
