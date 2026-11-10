import Erdos345.PowerSubsetSupport
import Erdos345.FiniteEventBounds

namespace Erdos345

open Filter

theorem mean_bad_support_le_cosineMean (R : Finset ℕ) (k q : ℕ) [NeZero q]
    {M : ℕ} (j : Fin M) :
    uniformMean (fun ω : R → Fin M => eventIndicator
      (((representedResidues (sampledBases R ω j) k q).card : ℝ) < (q : ℝ) / 4)) ≤
        uniformMean (fun ω : R → Fin M => subsetCosineSum (sampledBases R ω j) k q) / 3 := by
  apply uniformMean_event_le _ _ 3 (by norm_num)
  · intro ω
    exact subsetCosineSum_nonneg _ _ _
  · intro ω hbad
    by_contra hnot
    have hsmall : subsetCosineSum (sampledBases R ω j) k q ≤ 3 := by linarith
    have hsupport := representedResidues_large_of_cosineSum (sampledBases R ω j) k q hsmall
    linarith

/-- The probability, expressed as an exact finite average, that a
labelled group represents fewer than a quarter of the residues is
controlled by the uniform energy estimate. -/
theorem mean_bad_support_of_parameters (C : ℝ) (k : ℕ) (w : ℕ → ℕ)
    (hp : FourierParameterConditions C k w)
    (hw : AntitoneOn w (Set.Iio (k + 1))) (hmass : weightMass (k + 1) w = k + 1)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      (k : ℝ) ^ 2 < centerEnergy k u b (quasipolynomialCenterPrefix k C))
    (c : ℕ) (hc : 0 < c) (hcN : c ≤ fourierN k) (j : Fin 8192) :
    uniformMean (fun ω : unreservedPopulation (fourierN k) k → Fin 8192 => eventIndicator
      (((representedResidues (sampledBases (unreservedPopulation (fourierN k) k) ω j)
        k (c ^ k)).card : ℝ) < ((c ^ k : ℕ) : ℝ) / 4)) ≤
          Real.exp (-(k : ℝ) * logScale k ^ 8) / 3 := by
  let _ : NeZero (c ^ k) := ⟨Nat.ne_of_gt (pow_pos hc _)⟩
  exact (mean_bad_support_le_cosineMean (unreservedPopulation (fourierN k) k) k (c ^ k) j).trans
    (div_le_div_of_nonneg_right (mean_label_cosine_decay_of_parameters C k w hp hw hmass
      hcenter c hc hcN j) (by norm_num))

theorem good_degrees_label_support_small
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ c : ℕ, 0 < c → c ≤ fourierN k → ∀ j : Fin 8192,
        uniformMean (fun ω : unreservedPopulation (fourierN k) k → Fin 8192 => eventIndicator
          (((representedResidues (sampledBases (unreservedPopulation (fourierN k) k) ω j)
            k (c ^ k)).card : ℝ) < ((c ^ k : ℕ) : ℝ) / 4)) < ε := by
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp
    (eventually_fourier_parameter_conditions flatNormConstant flatNormConstant_nonneg)
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (eventually_fourier_decay_small ε hε)
  refine ⟨max 1 (max K₁ K₂), ?_⟩
  intro Y hY
  have hYpos : 0 < Y := by omega
  obtain ⟨k, hkY, hk2Y, hcenter⟩ := exists_good_center_bound_from_cosine_existence hinput Y hYpos
  have hkpos : 0 < k := hYpos.trans_le hkY
  obtain ⟨w, hw, hmass, hnorm⟩ := flat_family_from_cosine_existence hinput k hkpos k hkpos le_rfl
  have hp := hK₁ k (by omega) w hmass hnorm
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro c hc hcN j
  have hb := mean_bad_support_of_parameters flatNormConstant k w hp hw hmass hcenter c hc hcN j
  have hsmall : Real.exp (-(k : ℝ) * logScale k ^ 8) / 3 ≤
      Real.exp (-(k : ℝ) * logScale k ^ 8) := by nlinarith [Real.exp_pos (-(k : ℝ) * logScale k ^ 8)]
  exact (hb.trans hsmall).trans_lt (hK₂ k (by omega))

end Erdos345
