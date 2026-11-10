import Erdos345.PrefixGrowth

namespace Erdos345

noncomputable def centerPrefixPowerConstant (C : ℝ) : ℝ := 2 * C + centerPrefixLogConstant + 2

noncomputable def quasipolynomialCenterPrefix (k : ℕ) (C : ℝ) : ℕ :=
  Nat.ceil (Real.exp (centerPrefixPowerConstant C * logScale k ^ 6))

theorem log_sufficientCenterPrefix_exp_bound (Y k : ℕ) (hk : 0 < k) (hYk : Y ≤ k)
    (C : ℝ) (hC : 0 ≤ C) :
    Real.log (sufficientCenterPrefix k
      (sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k))
      (Real.exp (C * logScale k ^ 6)) ((k : ℝ) ^ 2) : ℝ) ≤
        centerPrefixPowerConstant C * logScale k ^ 6 := by
  let K := logScale k
  have hK : 1 ≤ K := logScale_ge_one k hk
  have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
  have hK56 : K ^ 5 ≤ K ^ 6 := pow_le_pow_right₀ hK (by decide)
  have hB1 : 1 ≤ Real.exp (C * K ^ 6) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hC (pow_nonneg (by linarith) _))
  have hlogB : Real.log (Real.exp (C * K ^ 6) + 1) ≤ Real.log 2 + C * K ^ 6 := by
    have h := Real.log_le_log (by positivity : 0 < Real.exp (C * K ^ 6) + 1)
      (show Real.exp (C * K ^ 6) + 1 ≤ 2 * Real.exp (C * K ^ 6) by linarith)
    rwa [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpoly := mul_le_mul_of_nonneg_left hK56 centerPrefixLogConstant_nonneg
  have h := log_sufficientCenterPrefix_square_le Y k hk hYk (Real.exp (C * K ^ 6)) (Real.exp_pos _).le
  change _ ≤ centerPrefixPowerConstant C * K ^ 6
  unfold centerPrefixPowerConstant
  change Real.log (sufficientCenterPrefix k
    (sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k))
    (Real.exp (C * K ^ 6)) ((k : ℝ) ^ 2) : ℝ) ≤ _ at h
  nlinarith

theorem sufficientCenterPrefix_le_quasipolynomial (Y k : ℕ) (hk : 0 < k) (hYk : Y ≤ k)
    (C : ℝ) (hC : 0 ≤ C) :
    sufficientCenterPrefix k
      (sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k))
      (Real.exp (C * logScale k ^ 6)) ((k : ℝ) ^ 2) ≤ quasipolynomialCenterPrefix k C := by
  have hpos : (0 : ℝ) < (sufficientCenterPrefix k
      (sufficientCenterWindow k ((k : ℝ) ^ 2) (goodConductorEnvelope Y k))
      (Real.exp (C * logScale k ^ 6)) ((k : ℝ) ^ 2) : ℝ) := by
    exact_mod_cast sufficientCenterPrefix_pos k _ _ _ (sq_nonneg (k : ℝ))
  have h := (Real.log_le_iff_le_exp hpos).mp (log_sufficientCenterPrefix_exp_bound Y k hk hYk C hC)
  have hceil := h.trans (Nat.le_ceil _)
  change _ ≤ (quasipolynomialCenterPrefix k C : ℝ) at hceil
  exact_mod_cast hceil

theorem centerEnergy_mono (k u q : ℕ) {X Z : ℕ} (hXZ : X ≤ Z) :
    centerEnergy k u q X ≤ centerEnergy k u q Z := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hXZ)
  intro n _ _
  exact centerTerm_nonneg k u q n

/-- A simple common prefix suffices for every primitive factorial
conductor at one degree in each dyadic interval, provided the displayed
finite flat family has the required small coefficient norm. -/
theorem exists_good_quasipolynomial_center_bound (Y : ℕ) (hY : 0 < Y) (C : ℝ) (hC : 0 ≤ C) :
    ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ((∀ d : ℕ, 0 < d → d ≤ k → ∃ w : ℕ → ℕ,
        AntitoneOn w (Set.Iio (d + 1)) ∧ weightMass (d + 1) w = d + 1 ∧
          coefficientL1 (flatPolynomial (d + 1) w) ≤ Real.exp (C * logScale k ^ 6)) →
      ∀ q u : ℕ, 1 < q → u.Coprime q → q ∣ k.factorial * (k + 1).factorial →
        (k : ℝ) ^ 2 < centerEnergy k u q (quasipolynomialCenterPrefix k C)) := by
  obtain ⟨k, hkY, hk2Y, hgood⟩ := exists_good_degree_explicit_center_bound Y hY
  have hk : 0 < k := hY.trans_le hkY
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro hflat q u hq hu hdiv
  have h := hgood (Real.exp (C * logScale k ^ 6)) ((k : ℝ) ^ 2) hflat q u hq hu hdiv
  exact h.trans_le (centerEnergy_mono k u q (sufficientCenterPrefix_le_quasipolynomial Y k hk hkY C hC))

end Erdos345
