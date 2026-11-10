import Erdos345.GoodConductorDegree

namespace Erdos345

noncomputable def centerWindowExponent (k : ℕ) (E H : ℝ) : ℝ :=
  4 * conductorCoefficient (k + 1) k *
    (2 * H + 2 * energyHeightConstant (k + 1) (E / 4) + 16 * Real.log ((k + 1 : ℕ) : ℝ))

noncomputable def sufficientCenterWindow (k : ℕ) (E H : ℝ) : ℕ :=
  Nat.ceil (16 + 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi +
    Real.exp (centerWindowExponent k E H))

noncomputable def sufficientCenterPrefix (k W : ℕ) (B E : ℝ) : ℕ :=
  Nat.ceil (((W : ℝ) + 1) * (B ^ 2 * E / 4 + 1) + ((k + 1 : ℕ) : ℝ) ^ 2)

theorem sufficientCenterWindow_ge_sixteen (k : ℕ) (E H : ℝ) :
    (16 : ℝ) ≤ sufficientCenterWindow k E H := by
  have h := Nat.le_ceil (16 + 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi +
    Real.exp (centerWindowExponent k E H))
  change _ ≤ (sufficientCenterWindow k E H : ℝ) at h
  have hpos : 0 ≤ 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi := by positivity
  have hexp := (Real.exp_pos (centerWindowExponent k E H)).le
  linarith

theorem sufficientCenterWindow_large (k : ℕ) (E H : ℝ) :
    1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 ≤
      Real.pi * sufficientCenterWindow k E H := by
  have h := Nat.le_ceil (16 + 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi +
    Real.exp (centerWindowExponent k E H))
  change _ ≤ (sufficientCenterWindow k E H : ℝ) at h
  have hexp := (Real.exp_pos (centerWindowExponent k E H)).le
  have hdiv : 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi ≤
      sufficientCenterWindow k E H := by linarith
  have hmul := (div_le_iff₀ Real.pi_pos).mp hdiv
  simpa only [mul_comm] using hmul

theorem sufficientCenterWindow_contracts (k : ℕ) (E H : ℝ) :
    conductorCoefficient (k + 1) k *
      ((2 * H + 2 * energyHeightConstant (k + 1) (E / 4) +
        16 * Real.log ((k + 1 : ℕ) : ℝ)) / Real.log (sufficientCenterWindow k E H)) ≤ 1 / 4 := by
  have hW := sufficientCenterWindow_ge_sixteen k E H
  have hlogW : 0 < Real.log (sufficientCenterWindow k E H : ℝ) := Real.log_pos (by linarith)
  have h := Nat.le_ceil (16 + 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi +
    Real.exp (centerWindowExponent k E H))
  change _ ≤ (sufficientCenterWindow k E H : ℝ) at h
  have hpos : 0 ≤ 1024 * ((k + 1 : ℕ) : ℝ) ^ 8 * ((k + 1 : ℕ) : ℝ) ^ 4 / Real.pi := by positivity
  have hexp : Real.exp (centerWindowExponent k E H) ≤ sufficientCenterWindow k E H := by linarith
  have hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hlogW).mpr
  unfold centerWindowExponent at hlog
  nlinarith

theorem centerEnergy_gt_sufficientPrefix (q u k : ℕ) (hq : 1 < q) (hu : u.Coprime q)
    (hk : 0 < k) (B E H : ℝ) (hH : 0 ≤ H)
    (hflat : ∀ d : ℕ, 0 < d → d ≤ k → ∃ w : ℕ → ℕ,
      AntitoneOn w (Set.Iio (d + 1)) ∧ weightMass (d + 1) w = d + 1 ∧
        coefficientL1 (flatPolynomial (d + 1) w) ≤ B)
    (hlog : ∀ d : ℕ, 0 < d → d ≤ k → q ∣ reductionModulus k d → Real.log (q : ℝ) ≤ H * d) :
    E < centerEnergy k u q (sufficientCenterPrefix k (sufficientCenterWindow k E H) B E) := by
  exact centerEnergy_gt_of_flat_family q u k _ _ hq hu hk B E H hH hflat hlog
    (Nat.le_ceil _) (sufficientCenterWindow_ge_sixteen k E H)
    (sufficientCenterWindow_large k E H) (sufficientCenterWindow_contracts k E H)

/-- Every dyadic interval has a degree for which this explicit prefix
works for every primitive factorial conductor, conditional only on the
specified finite flat-product family. -/
theorem exists_good_degree_explicit_center_bound (Y : ℕ) (hY : 0 < Y) :
    ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ B E : ℝ,
        (∀ d : ℕ, 0 < d → d ≤ k → ∃ w : ℕ → ℕ,
          AntitoneOn w (Set.Iio (d + 1)) ∧ weightMass (d + 1) w = d + 1 ∧
            coefficientL1 (flatPolynomial (d + 1) w) ≤ B) →
        ∀ q u : ℕ, 1 < q → u.Coprime q → q ∣ k.factorial * (k + 1).factorial →
          E < centerEnergy k u q
            (sufficientCenterPrefix k (sufficientCenterWindow k E (goodConductorEnvelope Y k)) B E) := by
  obtain ⟨k, hkY, hk2Y, hgood⟩ := exists_good_conductor_degree Y hY
  have hk : 0 < k := hY.trans_le hkY
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro B E hflat q u hq hu hdiv
  exact centerEnergy_gt_sufficientPrefix q u k hq hu hk B E (goodConductorEnvelope Y k)
    (goodConductorEnvelope_nonneg Y k hk) hflat (hgood q (by omega) hdiv)

end Erdos345
