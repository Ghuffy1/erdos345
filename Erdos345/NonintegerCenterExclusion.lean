import Erdos345.RationalCenters

namespace Erdos345

/-- If every noninteger primitive divisor-center has high energy, a
low-energy phase cannot be close to a noninteger rational center once
the displayed perturbation budget is satisfied. -/
theorem low_energy_center_numerator_divisible (k X B : ℕ) (hB : 0 < B)
    (E H r α : ℝ)
    (hcenter : ∀ q v : ℕ, 1 < q → v.Coprime q → q ∣ B → E < centerEnergy k v q X)
    (henergy : sineEnergy (fun n => α * (n : ℝ) ^ k) X ≤ H)
    (u : ℤ) (hnear : |α - (u : ℝ) / B| ≤ r)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * r ^ 2 * ((X : ℝ) ^ k) ^ 2 ≤ E) :
    (B : ℤ) ∣ u := by
  by_contra hnot
  have hhigh := rational_center_energy_gt k X B hB E hcenter u hnot
  have hlow := power_sineEnergy_perturbation ((u : ℝ) / B) α k X
  have hr : 0 ≤ r := (abs_nonneg _).trans hnear
  have hsq : ((u : ℝ) / B - α) ^ 2 ≤ r ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hnear 2
    simpa only [sq_abs, sub_sq_comm] using h
  have herror := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ 2 * Real.pi ^ 2 * (X : ℝ) * ((X : ℝ) ^ k) ^ 2 by positivity)
  nlinarith

theorem integer_near_of_numerator_divisible (B : ℕ) (hB : 0 < B) (u : ℤ)
    (hdiv : (B : ℤ) ∣ u) (α r : ℝ) (hnear : |α - (u : ℝ) / B| ≤ r) :
    ∃ z : ℤ, |α - (z : ℝ)| ≤ r := by
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z, ?_⟩
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hquot : (u : ℝ) / B = (z : ℝ) := by
    rw [hz, Int.cast_mul, Int.cast_natCast]
    field_simp
  simpa only [hquot] using hnear

theorem low_energy_near_factorial_center_is_near_integer (k X B : ℕ) (hB : 0 < B)
    (hBdiv : B ∣ k.factorial * (k + 1).factorial) (E H r α : ℝ)
    (hcenter : ∀ q v : ℕ, 1 < q → v.Coprime q → q ∣ k.factorial * (k + 1).factorial →
      E < centerEnergy k v q X)
    (henergy : sineEnergy (fun n => α * (n : ℝ) ^ k) X ≤ H)
    (u : ℤ) (hnear : |α - (u : ℝ) / B| ≤ r)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * r ^ 2 * ((X : ℝ) ^ k) ^ 2 ≤ E) :
    ∃ z : ℤ, |α - (z : ℝ)| ≤ r := by
  have hdiv := low_energy_center_numerator_divisible k X B hB E H r α
    (fun q v hq hv hd => hcenter q v hq hv (hd.trans hBdiv)) henergy u hnear hbudget
  exact integer_near_of_numerator_divisible B hB u hdiv α r hnear

/-- The finite inverse and the central-energy exclusion composed on a
trimmed prefix. Every quantitative size and perturbation condition is
visible; no asymptotic compatibility is assumed silently. -/
theorem flat_inverse_integer_center (N : ℕ) (w : ℕ → ℕ) (k V W X : ℕ)
    (hw : AntitoneOn w (Set.Iio N)) (hmass : weightMass N w = k + 1)
    (α H E : ℝ) (henergy : sineEnergy (fun n => α * (n : ℝ) ^ k) V ≤ H)
    (hXV : X ≤ V) (hW : 0 < W)
    (hlarge : 256 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hsize : ((W : ℝ) + 1) * (coefficientL1 (flatPolynomial N w) ^ 2 * H / 4 + 1) +
      (flatPolynomial N w).natDegree ≤ V)
    (hcenter : ∀ q v : ℕ, 1 < q → v.Coprime q → q ∣ k.factorial * (k + 1).factorial →
      E < centerEnergy k v q X)
    (hbudget : 2 * H + 2 * Real.pi ^ 2 * (X : ℝ) * (flatInverseRadius k W H) ^ 2 *
      ((X : ℝ) ^ k) ^ 2 ≤ E) :
    ∃ z : ℤ, |α - (z : ℝ)| ≤ flatInverseRadius k W H := by
  obtain ⟨hB, hBdiv, u, hnear⟩ := flat_inverse_of_energy_le N w k V W hw hmass α H
    henergy hW hlarge hsize
  have htrim := (sineEnergy_mono (fun n => α * (n : ℝ) ^ k) hXV).trans henergy
  exact low_energy_near_factorial_center_is_near_integer k X (k.factorial * normalizedMoment N w)
    hB hBdiv E H (flatInverseRadius k W H) α hcenter htrim u hnear hbudget

end Erdos345
