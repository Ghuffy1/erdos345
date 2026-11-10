import Erdos345.FourierParameterConditions
import Erdos345.SamplingRatio

namespace Erdos345

open Filter

theorem collision_decay_of_parameters (C : ℝ) (k : ℕ) (w : ℕ → ℕ)
    (hp : FourierParameterConditions C k w)
    (hw : AntitoneOn w (Set.Iio (k + 1))) (hmass : weightMass (k + 1) w = k + 1)
    (hcenter : ∀ b u : ℕ, 1 < b → u.Coprime b → b ∣ k.factorial * (k + 1).factorial →
      (k : ℝ) ^ 2 < centerEnergy k u b (quasipolynomialCenterPrefix k C))
    (c : ℕ) (hc : 0 < c) (hcN : c ≤ fourierN k) :
    powerCollisionSum (unreservedPopulation (fourierN k) k) k (c ^ k) (fourierT k) ≤
      Real.exp (-(k : ℝ) * logScale k ^ 8) := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hp.degree_large
  have hcoarse := hp.coarse_window
  have hH := fourierH_nonneg k
  have hkH := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hH
  have hWN : (fourierW k : ℝ) ≤ fourierN k := by exact_mod_cast fourierW_le_N k
  have hbase : 128000 * (k : ℝ) ≤ fourierN k := by nlinarith
  have hNk : 32 * (k : ℝ) ≤ fourierN k := by linarith
  have hN : 16384 ≤ fourierN k := by
    have h : (16384 : ℝ) ≤ fourierN k := by linarith
    exact_mod_cast h
  have hempty := (coarse_unreserved_frequency_bound (fourierN k) c k (k + 1)
    (fourierW k) (quasipolynomialCenterPrefix k C) w hc hcN hp.degree_large hw hmass
    (fourierH k) ((k : ℝ) ^ 2) hH (fourierW_le_N k) hp.coarse_window hp.center_inside
    hp.sampling_length hp.inverse_size hcenter hp.perturbation hp.root_budget).1
  have h := unreserved_collision_le_exp_margin (fourierN k) (c ^ k) k (fourierT k)
    hp.degree_large hNk (fourierH k) ((k : ℝ) * logScale k ^ 8) hempty
    (by simpa only [neg_mul] using fourier_collision_margin k c hp.degree_large hc hcN hN hNk)
  simpa only [neg_mul] using h

/-- Conditional only on the same cosine existence input as the center
theorem: every sufficiently large dyadic interval contains a degree
with uniform decay on all moduli c^k for 0<c<=N(k). -/
theorem good_degrees_fourier_decay
    (hinput : ∀ J : ℕ, 0 < J → ∃ w : ℕ → ℕ, ∃ a : ℝ,
      AntitoneOn w (Set.Iio J) ∧ weightMass J w = J ∧
      (∀ θ : ℝ, 0 ≤ a + ∑ i ∈ Finset.range J,
        (w i : ℝ) * Real.cos (((i + 1 : ℕ) : ℝ) * θ)) ∧
      a ≤ (2 : ℝ) ^ 32 * (1 + Real.log (J : ℝ)) ^ 5) :
    ∃ K : ℕ, ∀ Y : ℕ, K ≤ Y → ∃ k : ℕ, Y ≤ k ∧ k ≤ 2 * Y ∧
      ∀ c : ℕ, 0 < c → c ≤ fourierN k →
        powerCollisionSum (unreservedPopulation (fourierN k) k) k (c ^ k) (fourierT k) ≤
          Real.exp (-(k : ℝ) * logScale k ^ 8) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_fourier_parameter_conditions flatNormConstant flatNormConstant_nonneg)
  refine ⟨max 1 K, ?_⟩
  intro Y hY
  have hYpos : 0 < Y := by omega
  obtain ⟨k, hkY, hk2Y, hcenter⟩ := exists_good_center_bound_from_cosine_existence hinput Y hYpos
  have hkpos : 0 < k := hYpos.trans_le hkY
  obtain ⟨w, hw, hmass, hnorm⟩ := flat_family_from_cosine_existence hinput k hkpos k hkpos le_rfl
  have hparams := hK k (by omega) w hmass hnorm
  refine ⟨k, hkY, hk2Y, ?_⟩
  intro c hc hcN
  exact collision_decay_of_parameters flatNormConstant k w hparams hw hmass hcenter c hc hcN

end Erdos345
