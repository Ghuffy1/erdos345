import Erdos345.WindowHeightBudget

namespace Erdos345

open Finset Polynomial

/-- A finite analytic-to-arithmetic interface. All interval, energy,
small-height and numerical conductor-budget hypotheses remain explicit. -/
theorem rational_phase_window_reduction
    {N : ℕ} {w : ℕ → ℕ} (hw : AntitoneOn w (Set.Iio N))
    (hN : 1 ≤ N) (hMass : weightMass N w ≤ N)
    (k : ℕ) (hk : 0 < k) (hMassK : weightMass N w ≤ k + 1)
    (g : ℕ → ℤ) (P : ℚ[X]) (hdeg : P.natDegree < weightMass N w)
    (hg : shiftAction (flatPolynomial N w) g = 0)
    (q u : ℕ) (hq : 0 < q) (hu : u.Coprime q)
    (hInt : integerValuedPolynomial (C (q : ℚ) * P))
    (hPmod : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k)
    (a L : ℕ) (hL : (16 : ℝ) ≤ L)
    (hlarge : 1024 * (N : ℝ) ^ 8 * (N : ℝ) ^ 4 ≤ Real.pi * L)
    (E : ℝ)
    (hE : (∑ j ∈ range L,
      ‖((P.eval ((a + j : ℕ) : ℚ) - (g (a + j) : ℚ) : ℚ) : ℂ)‖ ^ 2) ≤ E)
    (M : ℕ)
    (hsmall : windowHeightBudget N (weightMass N w) q L E ≤ k)
    (hbudget : conductorCoefficient N k * windowHeightBudget N (weightMass N w) q L E ≤ M) :
    q ∣ reductionModulus k M ∧ minimalReductionDegree q k ≤ M ∧
      hasGlobalIntegerPolynomialReduction q k M := by
  let f : ℕ → ℚ := fun j => P.eval (j : ℚ) - (g j : ℚ)
  have hphase : ∀ j : ℕ, f j + (g j : ℚ) = P.eval (j : ℚ) := by
    intro j
    simp only [f, sub_add_cancel]
  obtain ⟨m, hm, hmin, hprime, hroot⟩ := exists_rational_phase_height_bounds
    hw hMass g P hdeg hg q hq hInt a L hL hlarge E hE
  have hheight := height_bounds_to_uniform N (weightMass N w) q L m hL E hprime hroot
  have hrootk : m 1 ≤ k := by exact_mod_cast hheight.1.trans hsmall
  have hmk := flat_multiplicity_le_power_degree hw k hk hMassK m hm hrootk
  obtain ⟨z, hz⟩ := exists_integer_error_multiple f g P hphase q hInt
  have hdiv : q ∣ reductionModulus k M :=
    rational_error_conductor_divisibility (Icc 1 N) m f g z P q u k N M hq hu hmin
      hphase hz hPmod (mem_Icc.mpr ⟨le_rfl, hN⟩)
      (fun n hn => (mem_Icc.mp hn).2) hmk
      (windowHeightBudget N (weightMass N w) q L E)
      (windowHeightBudget_nonneg _ _ _ _ _) hheight.1 hheight.2 hbudget
  exact ⟨hdiv, minimalReductionDegree_le hdiv,
    (hasGlobalIntegerPolynomialReduction_iff_dvd q k M).mpr hdiv⟩

end Erdos345
