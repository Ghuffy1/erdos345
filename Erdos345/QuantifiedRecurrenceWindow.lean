import Erdos345.WindowBudgetBounds

namespace Erdos345

open Finset Polynomial

/-- A concrete prefix-length condition supplies the required recurrence
window. The original center energy, not a new projected energy, is used. -/
theorem exists_reduced_phase_long_window (N : ℕ) (w : ℕ → ℕ) (P : ℚ[X])
    (hdeg : P.natDegree < weightMass N w) (q u k X W : ℕ) (hq : 0 < q)
    (hmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k)
    (B E : ℝ) (hB : coefficientL1 (flatPolynomial N w) ≤ B)
    (hcenter : centerEnergy k u q X ≤ E)
    (hsize : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) +
      (N : ℝ) * weightMass N w ≤ X) :
    ∃ a L : ℕ, ∃ g : ℕ → ℤ, W ≤ L ∧ a + L ≤ X ∧
      shiftAction (flatPolynomial N w) g = 0 ∧
      (∑ j ∈ range L,
        ‖((P.eval ((a + j : ℕ) : ℚ) - (g (a + j) : ℚ) : ℚ) : ℂ)‖ ^ 2) ≤ E / 4 := by
  let D := (flatPolynomial N w).natDegree
  let b := coefficientL1 (flatPolynomial N w)
  let F := centerEnergy k u q X
  have hb : 0 ≤ b := coefficientL1_nonneg _
  have hB0 : 0 ≤ B := hb.trans hB
  have hF : 0 ≤ F := sum_nonneg (fun n _ => centerTerm_nonneg k u q n)
  have hE : 0 ≤ E := hF.trans hcenter
  have hD : (D : ℝ) ≤ (N : ℝ) * weightMass N w := by
    exact_mod_cast flatPolynomial_natDegree_le N w
  have hsize0 : (N : ℝ) * weightMass N w ≤ X := by
    have hpos : 0 ≤ ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) := by positivity
    linarith
  have hDX : D ≤ X := by exact_mod_cast hD.trans hsize0
  have hprod : b ^ 2 * F ≤ B ^ 2 * E :=
    mul_le_mul (by nlinarith) hcenter hF (sq_nonneg B)
  have hden : b ^ 2 * F / 4 + 1 ≤ B ^ 2 * E / 4 + 1 := by linarith
  have hdenpos : 0 < b ^ 2 * F / 4 + 1 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hden (show 0 ≤ (W : ℝ) + 1 by positivity)
  have hremain : ((W : ℝ) + 1) * (b ^ 2 * F / 4 + 1) ≤ ((X - D : ℕ) : ℝ) := by
    rw [Nat.cast_sub hDX]
    nlinarith
  have hfrac : (W : ℝ) + 1 ≤ ((X - D : ℕ) : ℝ) / (b ^ 2 * F / 4 + 1) :=
    (le_div_iff₀ hdenpos).mpr hremain
  obtain ⟨a, L, g, ha, hL, hg, _hmatch, henergy⟩ :=
    exists_reduced_phase_recurrence N w P hdeg q u k X hq hmod hDX
  have hWL : W ≤ L := by
    have hLR : (W : ℝ) ≤ L := by dsimp only [D, b, F] at hfrac; linarith
    exact_mod_cast hLR
  refine ⟨a, D + L, g, hWL.trans (Nat.le_add_left L D), ?_, hg, ?_⟩
  · change a + L ≤ X - D at ha
    omega
  · exact henergy.trans (by linarith)

end Erdos345
