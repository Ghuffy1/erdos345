import Erdos345.ConvolvedWindowEnergy

namespace Erdos345

theorem inverse_energy_mono_length (k : ℕ) (δ : ℝ) (W L : ℕ) (hWL : W ≤ L) :
    (W : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      (|δ| * (W : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 ≤
    (L : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      (|δ| * (L : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 := by
  gcongr

/-- A finite inverse theorem on the original power-phase prefix. The
denominator depends only on the chosen flat product, not on the phase. -/
theorem flat_inverse_energy (N : ℕ) (w : ℕ → ℕ) (k X W : ℕ)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (α : ℝ) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) *
      (coefficientL1 (flatPolynomial N w) ^ 2 * sineEnergy (fun n => α * (n : ℝ) ^ k) X / 4 + 1) +
        (flatPolynomial N w).natDegree ≤ X) :
    0 < k.factorial * normalizedMoment N w ∧
      k.factorial * normalizedMoment N w ∣ k.factorial * (k + 1).factorial ∧
      ∃ u : ℤ, (W : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
        (|α - (u : ℝ) / ((k.factorial * normalizedMoment N w : ℕ) : ℝ)| *
          (W : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 ≤ sineEnergy (fun n => α * (n : ℝ) ^ k) X / 4 := by
  let D := (flatPolynomial N w).natDegree
  let F := sineEnergy (fun n => α * (n : ℝ) ^ k) X
  let A := coefficientL1 (flatPolynomial N w) ^ 2 * F / 4 + 1
  have hF : 0 ≤ F := sineEnergy_nonneg _ _
  have hA : 0 < A := by dsimp only [A]; positivity
  have hD : D ≤ X := by
    have hnonneg : 0 ≤ ((W : ℝ) + 1) * A := by positivity
    have hDR : (D : ℝ) ≤ X := by change ((W : ℝ) + 1) * A + (D : ℝ) ≤ X at hsize; linarith
    exact_mod_cast hDR
  have hfrac : (W : ℝ) + 1 ≤ ((X - D : ℕ) : ℝ) / A := by
    apply (le_div_iff₀ hA).mpr
    rw [Nat.cast_sub hD]
    change ((W : ℝ) + 1) * A + (D : ℝ) ≤ X at hsize
    linarith
  obtain ⟨a, L, g, _ha, hL, hg, _hmatch, henergy⟩ :=
    exists_flat_power_recurrence N w k (by omega) α X hD
  have hWL : W ≤ L := by
    have hR : (W : ℝ) ≤ L := by change _ / A - 1 ≤ (L : ℝ) at hL; linarith
    exact_mod_cast hR
  have hLpos : 0 < L := hW.trans_le hWL
  have hlargeL : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * L :=
    hlarge.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hWL) Real.pi_pos.le)
  have hLT : L + (flatQuotient N w).natDegree ≤ D + L := by
    have h := flatQuotient_natDegree_le N w
    dsimp only [D]
    omega
  obtain ⟨u, hu⟩ := inverse_energy_from_flat_recurrence N w g k hmass hg α a L (D + L)
    hLT hLpos hlargeL (F / 4) henergy
  have hMdiv := normalizedMoment_dvd_factorial hw
  rw [hmass] at hMdiv
  refine ⟨mul_pos (Nat.factorial_pos k) (normalizedMoment_pos N w),
    Nat.mul_dvd_mul_left k.factorial hMdiv, u, ?_⟩
  exact (inverse_energy_mono_length k
    (α - (u : ℝ) / ((k.factorial * normalizedMoment N w : ℕ) : ℝ)) W L hWL).trans hu

end Erdos345
