import Erdos345.ReductionConstantBounds

namespace Erdos345

/-- A finite central-energy criterion. The flat-product family and every
numerical input remain hypotheses; no asymptotic or external theorem is
silently assumed. The proof uses the actual least reduction degree. -/
theorem centerEnergy_gt_of_flat_family (q u k X W : ℕ)
    (hq : 1 < q) (hu : u.Coprime q) (hk : 0 < k) (B E H : ℝ) (hH : 0 ≤ H)
    (hflat : ∀ d : ℕ, 0 < d → d ≤ k → ∃ w : ℕ → ℕ,
      AntitoneOn w (Set.Iio (d + 1)) ∧ weightMass (d + 1) w = d + 1 ∧
        coefficientL1 (flatPolynomial (d + 1) w) ≤ B)
    (hlog : ∀ d : ℕ, 0 < d → d ≤ k → q ∣ reductionModulus k d →
      Real.log (q : ℝ) ≤ H * d)
    (hsize : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + ((k + 1 : ℕ) : ℝ) ^ 2 ≤ X)
    (hW : (16 : ℝ) ≤ W)
    (hlarge : 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W)
    (hcontract : conductorCoefficient (k + 1) k *
      ((2 * H + 2 * energyHeightConstant (k + 1) (E / 4) +
        16 * Real.log ((k + 1 : ℕ) : ℝ)) / Real.log W) ≤ 1 / 4) :
    E < centerEnergy k u q X := by
  by_contra hnot
  have hcenter : centerEnergy k u q X ≤ E := le_of_not_gt hnot
  let d := minimalReductionDegree q k
  have hd : 0 < d := minimalReductionDegree_pos hq hk
  have hdk : d ≤ k := minimalReductionDegree_le_self q k
  have hred : q ∣ reductionModulus k d := minimalReductionDegree_spec q k
  have hq0 : 0 < q := by omega
  obtain ⟨w, hw, hmass, hB⟩ := hflat d hd hdk
  let R := energyHeightConstant (k + 1) (E / 4)
  let K := Real.log ((k + 1 : ℕ) : ℝ)
  let C := conductorCoefficient (k + 1) k
  let a := (2 * H + 2 * R + 16 * K) / Real.log W
  let T := windowHeightBudget (d + 1) (d + 1) q W (E / 4)
  have hR : 0 ≤ R := le_max_left _ _
  have hK : 0 ≤ K := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k + 1 by omega))
  have hlogW : 0 < Real.log (W : ℝ) := Real.log_pos (by linarith)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hC : 1 ≤ C := conductorCoefficient_ge_one _ _
  have hCa : C * a ≤ 1 / 4 := hcontract
  have hCN : conductorCoefficient (d + 1) k ≤ C :=
    conductorCoefficient_mono _ _ _ (Nat.succ_le_succ hdk)
  have hT : T ≤ a * d := by
    apply windowHeightBudget_le_linear_degree d (d + 1) q W hd hq0 hW le_rfl
    · exact energyHeightConstant_mono _ _ (by omega) (Nat.succ_le_succ hdk) (E / 4)
    · exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hdk)
    · exact hlog d hd hdk hred
  have hT0 : 0 ≤ T := windowHeightBudget_nonneg _ _ _ _ _
  have hbudget : conductorCoefficient (d + 1) k * T ≤ (d : ℝ) / 4 := by
    calc
      _ ≤ C * (a * d) := mul_le_mul hCN hT hT0 (le_trans (by norm_num) hC)
      _ = (C * a) * d := by ring
      _ ≤ (1 / 4 : ℝ) * d := mul_le_mul_of_nonneg_right hCa (Nat.cast_nonneg _)
      _ = _ := by ring
  have hTfactor : T ≤ conductorCoefficient (d + 1) k * T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (conductorCoefficient_ge_one (d + 1) k) hT0
  have hTquarter : T ≤ (d : ℝ) / 4 := hTfactor.trans hbudget
  have hsmall : T ≤ k := by
    have hdkR : (d : ℝ) ≤ k := by exact_mod_cast hdk
    linarith
  have hsizeD : ((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + ((d + 1 : ℕ) : ℝ) ^ 2 ≤ X := by
    have hquad : (((d + 1 : ℕ) : ℝ) ^ 2) ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
      gcongr
    linarith
  have hlargeD : 1024 * ((d + 1 : ℕ) : ℝ) ^ 8 * ((d + 1 : ℕ) : ℝ) ^ 4 ≤ Real.pi * W := by
    refine le_trans ?_ hlarge
    gcongr
  obtain ⟨M, hM, hMbound⟩ := exists_exact_reduction_step q u k d X W hq0 hu hk hdk hred
    w hw hmass B E hB hcenter hsizeD hW hlargeD hsmall
  have hdM : (d : ℝ) ≤ M := by exact_mod_cast minimalReductionDegree_le hM
  have hdsmall : (d : ℝ) < 2 := by
    change (M : ℝ) < conductorCoefficient (d + 1) k * T + 1 at hMbound
    linarith
  have hd1 : d = 1 := by
    have : d < 2 := by exact_mod_cast hdsmall
    omega
  have hTone : T < 1 := by rw [hd1] at hTquarter; norm_num at hTquarter; linarith
  have hqone := exact_reduction_step_modulus_one q u k d X W hq0 hu hred w hw hmass
    B E hB hcenter hsizeD hW hlargeD hTone
  omega

end Erdos345
