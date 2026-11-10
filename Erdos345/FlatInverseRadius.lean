import Erdos345.FlatInverseEnergy

namespace Erdos345

noncomputable def flatInverseRadius (k W : ℕ) (E : ℝ) : ℝ :=
  (4 : ℝ) ^ k / (W : ℝ) ^ k * Real.sqrt (16 * ((k + 1 : ℕ) : ℝ) * E / (Real.pi * W))

theorem abs_le_flatInverseRadius (k W : ℕ) (hW : 0 < W) (δ E : ℝ) (hE : 0 ≤ E)
    (henergy : (W : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
      (|δ| * (W : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 ≤ E / 4) :
    |δ| ≤ flatInverseRadius k W E := by
  let A := (W : ℝ) ^ k / (4 : ℝ) ^ k
  let c := (W : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ)))
  let R := 16 * ((k + 1 : ℕ) : ℝ) * E / (Real.pi * W)
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hA : 0 < A := by dsimp only [A]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hscale : (E / 4) / c = R := by dsimp only [c, R]; field_simp; ring
  have henergy' : c * (|δ| * A) ^ 2 ≤ E / 4 := by
    calc
      _ = (W : ℝ) * (Real.pi / (64 * ((k + 1 : ℕ) : ℝ))) *
          (|δ| * (W : ℝ) ^ k / (4 : ℝ) ^ k) ^ 2 := by dsimp only [A, c]; ring
      _ ≤ _ := henergy
  have hquad : (|δ| * A) ^ 2 ≤ R := by
    rw [← hscale]
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  have hsqrt : |δ| * A ≤ Real.sqrt R := by
    have h := Real.sq_sqrt hR
    have hpos := Real.sqrt_nonneg R
    nlinarith [mul_nonneg (abs_nonneg δ) hA.le]
  calc
    |δ| ≤ Real.sqrt R / A := (le_div_iff₀ hA).mpr hsqrt
    _ = flatInverseRadius k W E := by
      dsimp only [R, A, flatInverseRadius]
      field_simp

/-- Uniform rational approximation for every phase below the same energy
cutoff. The common denominator is fixed before choosing the phase. -/
theorem flat_inverse_of_energy_le (N : ℕ) (w : ℕ → ℕ) (k X W : ℕ)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (α E : ℝ) (henergy : sineEnergy (fun n => α * (n : ℝ) ^ k) X ≤ E)
    (hW : 0 < W) (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * E / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ X) :
    0 < k.factorial * normalizedMoment N w ∧
      k.factorial * normalizedMoment N w ∣ k.factorial * (k + 1).factorial ∧
      ∃ u : ℤ, |α - (u : ℝ) / ((k.factorial * normalizedMoment N w : ℕ) : ℝ)| ≤
        flatInverseRadius k W E := by
  have hE : 0 ≤ E := (sineEnergy_nonneg _ _).trans henergy
  have hsize' : ((W : ℝ) + 1) *
      (coefficientL1 (flatPolynomial N w) ^ 2 * sineEnergy (fun n => α * (n : ℝ) ^ k) X / 4 + 1) +
        (flatPolynomial N w).natDegree ≤ X := by
    have h := mul_le_mul_of_nonneg_left henergy (sq_nonneg (coefficientL1 (flatPolynomial N w)))
    have h' := mul_le_mul_of_nonneg_left (show coefficientL1 (flatPolynomial N w) ^ 2 *
        sineEnergy (fun n => α * (n : ℝ) ^ k) X / 4 + 1 ≤
      coefficientL1 (flatPolynomial N w) ^ 2 * E / 4 + 1 by linarith)
      (show 0 ≤ (W : ℝ) + 1 by positivity)
    linarith
  obtain ⟨hB, hdiv, u, hu⟩ := flat_inverse_energy N w k X W hw hmass α hW hlarge hsize'
  refine ⟨hB, hdiv, u, ?_⟩
  exact abs_le_flatInverseRadius k W hW _ E hE (hu.trans (by linarith))

end Erdos345
