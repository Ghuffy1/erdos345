import Erdos345.QuantifiedRecurrenceWindow

namespace Erdos345

open Finset Polynomial

/-- A full finite reduction step, starting with the original center energy
and a supplied flat product, rather than an assumed recurrence window. -/
theorem exact_reduction_step (q u k d X W M : ℕ)
    (hq : 0 < q) (hu : u.Coprime q) (hk : 0 < k) (hdk : d ≤ k)
    (hred : q ∣ reductionModulus k d)
    (w : ℕ → ℕ) (hw : AntitoneOn w (Set.Iio (d + 1)))
    (hmass : weightMass (d + 1) w = d + 1)
    (B E : ℝ) (hB : coefficientL1 (flatPolynomial (d + 1) w) ≤ B)
    (hcenter : centerEnergy k u q X ≤ E)
    (hsize : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + ((d + 1 : ℕ) : ℝ) ^ 2 ≤ X)
    (hW : (16 : ℝ) ≤ W)
    (hlarge : 1024 * ((d + 1 : ℕ) : ℝ) ^ 8 * ((d + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsmall : windowHeightBudget (d + 1) (d + 1) q W (E / 4) ≤ k)
    (hbudget : conductorCoefficient (d + 1) k *
      windowHeightBudget (d + 1) (d + 1) q W (E / 4) ≤ M) :
    q ∣ reductionModulus k M := by
  obtain ⟨P, hdegree, hInt, hmod⟩ := exists_rational_reduction_phase q u k d hq hred
  have hdeg : P.natDegree < weightMass (d + 1) w := by omega
  have hmodNat : ∀ n : ℕ, ∃ A : ℤ, (q : ℚ) * P.eval (n : ℚ) = (A : ℚ) ∧
      (q : ℤ) ∣ A - (u : ℤ) * (n : ℤ) ^ k := by
    intro n
    simpa only [Int.cast_natCast] using hmod (n : ℤ)
  have hsize' : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) +
      ((d + 1 : ℕ) : ℝ) * weightMass (d + 1) w ≤ X := by
    rw [hmass]
    simpa only [pow_two] using hsize
  obtain ⟨a, L, g, hWL, _ha, hg, henergy⟩ := exists_reduced_phase_long_window
    (d + 1) w P hdeg q u k X W hq hmodNat B E hB hcenter hsize'
  have hLR : (W : ℝ) ≤ L := by exact_mod_cast hWL
  have hL : (16 : ℝ) ≤ L := hW.trans hLR
  have hlargeL : 1024 * ((d + 1 : ℕ) : ℝ) ^ 8 * ((d + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * L :=
    hlarge.trans (mul_le_mul_of_nonneg_left hLR Real.pi_pos.le)
  have hT := windowHeightBudget_antitone_length (d + 1) (d + 1) q W L (by omega) hq hW hWL (E / 4)
  have hC : 0 ≤ conductorCoefficient (d + 1) k :=
    le_trans (by norm_num) (conductorCoefficient_ge_one _ _)
  have hsmallL : windowHeightBudget (d + 1) (weightMass (d + 1) w) q L (E / 4) ≤ k := by
    rw [hmass]
    exact hT.trans hsmall
  have hbudgetL : conductorCoefficient (d + 1) k *
      windowHeightBudget (d + 1) (weightMass (d + 1) w) q L (E / 4) ≤ M := by
    rw [hmass]
    exact (mul_le_mul_of_nonneg_left hT hC).trans hbudget
  exact (rational_phase_window_reduction hw (by omega) hmass.le k hk (by omega)
    g P hdeg hg q u hq hu hInt hmodNat a L hL hlargeL (E / 4) henergy M hsmallL hbudgetL).1

theorem exists_exact_reduction_step (q u k d X W : ℕ)
    (hq : 0 < q) (hu : u.Coprime q) (hk : 0 < k) (hdk : d ≤ k)
    (hred : q ∣ reductionModulus k d)
    (w : ℕ → ℕ) (hw : AntitoneOn w (Set.Iio (d + 1)))
    (hmass : weightMass (d + 1) w = d + 1)
    (B E : ℝ) (hB : coefficientL1 (flatPolynomial (d + 1) w) ≤ B)
    (hcenter : centerEnergy k u q X ≤ E)
    (hsize : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + ((d + 1 : ℕ) : ℝ) ^ 2 ≤ X)
    (hW : (16 : ℝ) ≤ W)
    (hlarge : 1024 * ((d + 1 : ℕ) : ℝ) ^ 8 * ((d + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsmall : windowHeightBudget (d + 1) (d + 1) q W (E / 4) ≤ k) :
    ∃ M : ℕ, q ∣ reductionModulus k M ∧ (M : ℝ) <
      conductorCoefficient (d + 1) k * windowHeightBudget (d + 1) (d + 1) q W (E / 4) + 1 := by
  let R := conductorCoefficient (d + 1) k * windowHeightBudget (d + 1) (d + 1) q W (E / 4)
  have hR : 0 ≤ R := mul_nonneg
    (le_trans (by norm_num) (conductorCoefficient_ge_one _ _)) (windowHeightBudget_nonneg _ _ _ _ _)
  refine ⟨Nat.ceil R, ?_, Nat.ceil_lt_add_one hR⟩
  exact exact_reduction_step q u k d X W (Nat.ceil R) hq hu hk hdk hred w hw hmass
    B E hB hcenter hsize hW hlarge hsmall (Nat.le_ceil R)

end Erdos345
